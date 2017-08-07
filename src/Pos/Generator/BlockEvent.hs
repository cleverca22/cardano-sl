{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pos.Generator.BlockEvent
       (
       -- * Util
         IsBlockEventFailure(..)
       -- * Block apply
       , BlockApplyResult(..)
       , BlockEventApply'(..)
       , BlockEventApply
       , beaInput
       , beaOutValid
       -- * Block rollback
       , BlockRollbackResult(..)
       , BlockEventRollback'(..)
       , BlockEventRollback
       , berInput
       , berOutValid
       -- * Snapshot management
       , SnapshotId(..)
       , SnapshotOperation(..)
       , enrichWithSnapshotChecking
       , CheckCount(..)
       -- * Block event sum
       , BlockEvent'(..)
       , BlockEvent
       -- * Block scenario
       , BlockScenario'(..)
       , BlockScenario
       , _BlockScenario
       -- * Path
       , PathSegment(..)
       , Path(..)
       , pathSequence
       -- * Chance
       , Chance(..)
       , byChance
       -- * Block description
       , BlockDesc(..)
       -- * Generation
       , MonadGenBlockchain
       , BlockEventCount(..)
       , BlockEventGenParams(..)
       , begpBlockCountMax
       , begpBlockEventCount
       , begpRollbackChance
       , begpFailureChance
       , begpSecrets
       , genBlockScenario
       , genBlocksInStructure
       ) where

import           Universum

import           Control.Lens                (foldMapOf, folded, makeLenses, makePrisms)
import           Control.Monad.Random.Strict (MonadRandom (..), RandT, Random (..),
                                              RandomGen, mapRandT, runRand, uniform,
                                              weighted)
import           Control.Monad.State         (MonadState (..))
import           Data.Default                (def)
import qualified Data.List.NonEmpty          as NE
import qualified Data.Map                    as Map
import qualified Data.Semigroup              as Smg
import qualified Data.Sequence               as Seq
import qualified Data.Text.Buildable
import           Formatting                  (bprint, build, formatToString, int, sformat,
                                              shown, (%))
import qualified Prelude
import           Serokell.Util               (listJson)

import           Pos.Block.Types             (Blund)
import           Pos.Core                    (BlockCount (..), HeaderHash, headerHash,
                                              prevBlockL)
import           Pos.Crypto.Hashing          (hashHexF)
import           Pos.Generator.Block         (AllSecrets, BlockGenParams (..),
                                              MonadBlockGen, TxGenParams, genBlocks)
import           Pos.GState.Context          (withClonedGState)
import           Pos.Ssc.GodTossing.Type     (SscGodTossing)
import           Pos.Util.Chrono             (NE, NewestFirst (..), OldestFirst (..),
                                              nonEmptyOldestFirst, splitAtNewestFirst,
                                              toNewestFirst, toOldestFirst, _NewestFirst,
                                              _OldestFirst)

type BlundDefault = Blund SscGodTossing

----------------------------------------------------------------------------
-- Blockchain tree
----------------------------------------------------------------------------

-- NB. not a monoid, so the user can be sure that `(<>)` acts as expected
-- on string literals for paths (not path segments).
newtype PathSegment = PathSegment Text
    deriving (Eq, Ord, IsString)

instance Show PathSegment where
    showsPrec p (PathSegment s) = Prelude.showsPrec p s

-- | Construct a path using string literals and monoidal/semigroupoidal
--   operations: @"first" <> "next"@, @stimes 15 "next"@.
--   An empty path does not point at any block, don't use it on its own! (but
--   it's a valid 'mempty')
newtype Path = Path (Seq PathSegment)
    deriving (Eq, Ord, Semigroup, Monoid)

instance IsString Path where
    fromString = Path . Seq.singleton . fromString

instance Buildable Path where
    build (Path segs) = bprint build (fold . Seq.intersperse "/" $ segs <&> \(PathSegment t) -> t)

-- | Convert a sequence of relative paths into a sequence of absolute paths:
--   @pathSequence "base" ["a", "b", "c"] = ["base" <> "a", "base" <> "a" <> "b", "base" <> "a" <> "b" <> "c"]
pathSequence ::
       Path -- ^ base path
    -> OldestFirst NE Path -- ^ relative paths
    -> OldestFirst NE Path -- ^ absolute paths
pathSequence basePath = over _OldestFirst $
    NE.fromList . fmap (mappend basePath . mconcat) . NE.tail . NE.inits

type BlockchainForest a = Map PathSegment (BlockchainTree a)

data BlockchainTree a = BlockchainTree a (BlockchainForest a)
  deriving (Show, Functor, Foldable)

data BlockDesc
    = BlockDescDefault -- a random valid block
    | BlockDescCustom TxGenParams -- a random valid block with custom gen params
    deriving (Show)

-- Precondition: input paths are non-empty
buildBlockchainForest :: a -> Map Path a -> BlockchainForest a
buildBlockchainForest defElem elements =
    fmap (buildBlockchainTree defElem) . Map.fromListWith Map.union $ do
        (Path path, a) <- Map.toList elements
        case Seq.viewl path of
            Seq.EmptyL -> error
                "buildBlockchainForest: precondition violated, empty path"
            pathSegment Seq.:< path' ->
                [(pathSegment, Map.singleton (Path path') a)]

buildBlockchainTree :: a -> Map Path a -> BlockchainTree a
buildBlockchainTree defElem elements =
    let
        topPath = Path Seq.empty
        topElement = Map.findWithDefault defElem topPath elements
        -- 'otherElements' has its empty path deleted (if there was one in the
        -- first place), so it satisfies the precondition of 'buildBlockchainForest'
        otherElements = Map.delete topPath elements
    in
        BlockchainTree topElement (buildBlockchainForest defElem otherElements)

-- Inverse to 'buildBlockchainForest'.
flattenBlockchainForest' :: BlockchainForest a -> Map Path a
flattenBlockchainForest' =
    Map.fromList . flattenBlockchainForest (Path Seq.empty)

flattenBlockchainForest :: Path -> BlockchainForest a -> [(Path, a)]
flattenBlockchainForest (Path prePath) forest = do
    (pathSegment, subtree) <- Map.toList forest
    flattenBlockchainTree (Path $ prePath Seq.|> pathSegment) subtree

flattenBlockchainTree :: Path -> BlockchainTree a -> [(Path, a)]
flattenBlockchainTree prePath tree = do
    let BlockchainTree a forest = tree
    (prePath, a) : flattenBlockchainForest prePath forest

type MonadGenBlockchain ctx m =
    ( MonadBlockGen ctx m
    , MonadThrow m )

genBlocksInForest ::
       (MonadGenBlockchain ctx m, RandomGen g)
    => AllSecrets
    -> BlockchainForest BlockDesc
    -> RandT g m (BlockchainForest BlundDefault)
genBlocksInForest secrets =
    traverse $ mapRandT withClonedGState . genBlocksInTree secrets

genBlocksInTree ::
       (MonadGenBlockchain ctx m, RandomGen g)
    => AllSecrets
    -> BlockchainTree BlockDesc
    -> RandT g m (BlockchainTree BlundDefault)
genBlocksInTree secrets blockchainTree = do
    let
        BlockchainTree blockDesc blockchainForest = blockchainTree
        txGenParams = case blockDesc of
            BlockDescDefault  -> def
            BlockDescCustom p -> p
        blockGenParams = BlockGenParams
            { _bgpSecrets     = secrets
            , _bgpBlockCount  = 1
            , _bgpTxGenParams = txGenParams
            , _bgpInplaceDB   = True
            }
    -- Partial pattern-matching is safe because we specify
    -- blockCount = 1 in the generation parameters.
    OldestFirst [block] <- genBlocks blockGenParams
    forestBlocks <- genBlocksInForest secrets blockchainForest
    return $ BlockchainTree block forestBlocks

-- Precondition: paths in the structure are non-empty.
genBlocksInStructure ::
       ( MonadGenBlockchain ctx m
       , Functor t, Foldable t
       , RandomGen g )
    => AllSecrets
    -> Map Path BlockDesc
    -> t Path
    -> RandT g m (t BlundDefault)
genBlocksInStructure secrets annotations s = do
    let
        getAnnotation path =
            Map.findWithDefault BlockDescDefault path annotations
        paths = foldMapOf folded
            (\path -> Map.singleton path (getAnnotation path))
            s
        descForest = buildBlockchainForest BlockDescDefault paths
    blockForest <- genBlocksInForest secrets descForest
    let
        getBlock path = Map.findWithDefault
            (error "genBlocksInStructure: impossible happened")
            path
            (flattenBlockchainForest' blockForest)
    return $ fmap getBlock s

----------------------------------------------------------------------------
-- Block event types
----------------------------------------------------------------------------

-- | Determine whether the result of a block event is an expected failure.
class IsBlockEventFailure a where
    isBlockEventFailure :: a -> Bool

data BlockApplyResult
    = BlockApplySuccess
    | BlockApplyFailure {- TODO: attach error info, such as:
                            * block is not a continuation of the chain
                            * block signature is invalid
                            * etc -}
    deriving (Show)

instance IsBlockEventFailure BlockApplyResult where
    isBlockEventFailure = \case
        BlockApplyFailure -> True
        _ -> False

data BlockEventApply' blund = BlockEventApply
    { _beaInput    :: !(OldestFirst NE blund)
    , _beaOutValid :: !BlockApplyResult
    } deriving (Show, Functor, Foldable)

makeLenses ''BlockEventApply'

instance IsBlockEventFailure (BlockEventApply' blund) where
    isBlockEventFailure = isBlockEventFailure . view beaOutValid

type BlockEventApply = BlockEventApply' BlundDefault

data BlockRollbackResult
    = BlockRollbackSuccess
    | BlockRollbackFailure {- TODO: attach error info, such as:
                                * not enough blocks to rollback
                                * rollback limit exceeded
                                * genesis block rollback
                                * etc -}
    deriving (Show)

instance IsBlockEventFailure BlockRollbackResult where
    isBlockEventFailure = \case
        BlockRollbackFailure -> True
        _ -> False

data BlockEventRollback' blund = BlockEventRollback
    { _berInput    :: !(NewestFirst NE blund)
    , _berOutValid :: !BlockRollbackResult
    } deriving (Show, Functor, Foldable)

makeLenses ''BlockEventRollback'

instance IsBlockEventFailure (BlockEventRollback' blund) where
    isBlockEventFailure = isBlockEventFailure . view berOutValid

type BlockEventRollback = BlockEventRollback' BlundDefault

newtype SnapshotId = SnapshotId Text
    deriving (Eq, Ord, IsString)

instance Show SnapshotId where
    showsPrec p (SnapshotId s) = Prelude.showsPrec p s

data SnapshotOperation
    = SnapshotSave SnapshotId {- Save the current db state into a snapshot
    under the specified identifier. Overwrites an existing snapshot with the
    same name or creates a new one. -}
    | SnapshotLoad SnapshotId {- Set the current db state to a state saved in
    a snapshot earlier. -}
    | SnapshotEq SnapshotId {- Compare the current db state to a state saved
    in a snapshot earlier, checking for equivalence. If logical discrepancies
    are found, throw an error. -}
    deriving (Show)

instance Buildable SnapshotOperation where
      build = bprint shown

data BlockEvent' blund
      = BlkEvApply (BlockEventApply' blund)
      | BlkEvRollback (BlockEventRollback' blund)
      | BlkEvSnap SnapshotOperation
      deriving (Show, Functor, Foldable)

instance Buildable blund => Buildable (BlockEvent' blund) where
    build = \case
        BlkEvApply ev -> bprint ("Apply blocks: "%listJson) (getOldestFirst $ ev ^. beaInput)
        BlkEvRollback ev -> bprint ("Rollback blocks: "%listJson) (getNewestFirst $ ev ^. berInput)
        BlkEvSnap s -> bprint build s

instance IsBlockEventFailure (BlockEvent' blund) where
    isBlockEventFailure = \case
        BlkEvApply    a -> isBlockEventFailure a
        BlkEvRollback a -> isBlockEventFailure a
        BlkEvSnap     _ -> False

type BlockEvent = BlockEvent' BlundDefault

newtype BlockScenario' blund = BlockScenario [BlockEvent' blund]
    deriving (Show, Functor, Foldable)

instance Buildable blund => Buildable (BlockScenario' blund) where
    build (BlockScenario xs) = bprint listJson xs

type BlockScenario = BlockScenario' BlundDefault

makePrisms ''BlockScenario'

----------------------------------------------------------------------------
-- Block event generation
----------------------------------------------------------------------------

newtype BlockEventCount = BlockEventCount {getBlockEventCount :: Word64}
    deriving (Eq, Ord, Num, Real, Integral, Enum, Read, Show,
              Buildable, Generic, Typeable, NFData, Hashable, Random)

-- | A coefficient in the range [0,1]. Pass it to 'weighted' if you ever get
-- the chance.
newtype Chance = Chance {getChance :: Rational}
    deriving (Buildable, Num, Fractional)

-- | Generate a boolean that may happen to be of true value.
byChance :: (Monad m, RandomGen g) => Chance -> RandT g m Bool
byChance (Chance c) = weighted [(False, 1 - c), (True, c)]

data BlockEventGenParams = BlockEventGenParams
    { _begpSecrets         :: !AllSecrets
    , _begpBlockCountMax   :: !BlockCount {- ^ the maximum possible amount of
    blocks in a BlockApply event. Must be 1 or more. Can be violated by 1 in
    some cases (see Note on reordering corner cases), so if you specify '52'
    here, some rare events may contain up to '53' blocks. -}
    , _begpBlockEventCount :: !BlockEventCount {- ^ the amount of events to
    generate excluding the last complete rollback event. There can be less
    events if we generate an expected failure. For example, if you specify '10'
    here, you'll either get 11 events (the last is a complete rollback) or
    some amount of events from 1 to 10 (the last is an expected failure).
    If you set the failure chance to '0', you'll always get the requested
    amount of events. -}
    , _begpRollbackChance  :: !Chance
    , _begpFailureChance   :: !Chance
    }

makeLenses ''BlockEventGenParams

instance Buildable BlockEventGenParams where
    build BlockEventGenParams {..} =
        bprint ("BlockEventGenParams {\n"%
                "  secrets: "%build%"\n"%
                "  block count max: "%int%"\n"%
                "  block event count: "%int%"\n"%
                "  rollback chance: "%build%"\n"%
                "  failure chance: "%build%"\n"%
                "}\n")
            _begpSecrets
            _begpBlockCountMax
            _begpBlockEventCount
            _begpRollbackChance
            _begpFailureChance

instance Show BlockEventGenParams where
    show = formatToString build

-- | Generate a random sequence of block events. The final event is either an
-- expected failure or a rollback of the entire chain to the initial (empty)
-- state. There's no forking at the moment.
genBlockScenario ::
       (MonadBlockGen ctx m, RandomGen g)
    => BlockEventGenParams
    -> RandT g m BlockScenario
genBlockScenario begp = do
    preBlockEvents <- genBlockEvents' begp
    genBlocksInStructure (begp ^. begpSecrets) Map.empty $
        BlockScenario preBlockEvents

data GenBlockEventState
    = GbesStartingState
    | GbesBlockchain (OldestFirst NE Path)
    | GbesExpectedFailure

-- | A version of 'genBlockEvents' that generates event with block paths
-- instead of actual blocks.
genBlockEvents' ::
       (Monad m, RandomGen g)
    => BlockEventGenParams
    -> RandT g m [BlockEvent' Path]
genBlockEvents' begp =
    flip evalStateT GbesStartingState $ do
        events <- replicateWhileM
            (fromIntegral $ begp ^. begpBlockEventCount)
            (genBlockEvent begp)
        finalEvent <- get <&> \case
            GbesStartingState -> []
            GbesExpectedFailure -> []
            GbesBlockchain blockchain ->
                -- Rollback the entire blockchain.
                [BlkEvRollback $ BlockEventRollback
                    { _berInput    = toNewestFirst blockchain
                    , _berOutValid = BlockRollbackSuccess
                    }]
        return $ events ++ finalEvent

replicateWhileM :: Monad m => Int -> m (Maybe a) -> m [a]
replicateWhileM n m = go n
  where
    go k | k < 1 = return []
         | otherwise =
             m >>= \case
                 Nothing -> return []
                 Just a  -> (a:) <$> go (k-1)

data RollbackFailureType
    = RftRollbackDrop
    deriving (Enum, Bounded)

instance Random RollbackFailureType where
    random = randomR (minBound, maxBound)
    randomR (lo,hi) = runRand $ uniform [lo..hi]

data ApplyFailureType
    = AftApplyBad
    | AftApplyNonCont
    deriving (Enum, Bounded)

instance Random ApplyFailureType where
    random = randomR (minBound, maxBound)
    randomR (lo,hi) = runRand $ uniform [lo..hi]

newtype IsFailure = IsFailure Bool
newtype IsRollback = IsRollback Bool

genBlockEvent ::
       (Monad m, RandomGen g)
    => BlockEventGenParams
    -> StateT GenBlockEventState (RandT g m) (Maybe (BlockEvent' Path))
genBlockEvent begp = do
    gbes <- get
    failure <- lift $ IsFailure <$> byChance (begp ^. begpFailureChance)
    rollback <- lift $ IsRollback <$> byChance (begp ^. begpRollbackChance)
    (mBlockEvent, gbes') <- case gbes of
        GbesExpectedFailure ->
            return (Nothing, gbes)
        GbesStartingState ->
            genBlockStartingState failure rollback
        GbesBlockchain blockchain ->
            genBlockInBlockchain blockchain failure rollback
    put gbes' $> mBlockEvent
  where
    genBlockIndices pathStart = do
        len <- getRandomR (1, fromIntegral $ begp ^. begpBlockCountMax)
        -- 'NE.fromList' assumes that 'len >= 1', which holds because we require
        -- 'begpBlockCountMax >= 1'.
        return $ OldestFirst . NE.fromList . take len $
            iterate (<> "next") pathStart
    -- Fail with rollback. In the starting state it's easy,
    -- because any rollback will fail when we don't have any
    -- blocks yet.
    genBlockStartingState (IsFailure True) (IsRollback True) = do
        blockIndices <- genBlockIndices "first"
        let
            ev = BlkEvRollback $ BlockEventRollback
                { _berInput    = toNewestFirst blockIndices
                , _berOutValid = BlockRollbackFailure
                }
            gbes = GbesExpectedFailure
        return (Just ev, gbes)
    -- Fail without rollback (with apply). In the starting state,
    -- the only way to do this is to generate a sequence of blocks
    -- invalid by itself.
    genBlockStartingState (IsFailure True) (IsRollback False) = do
        blockIndices <- genBlockIndices ("first" <> "next")
        let
            blkZeroth = "first" :| []
            blockIndices' =
                -- Those block indices are broken by construction
                -- because we append the 0-th block to the end.
                -- Sometimes we can violate the maximum bound on
                -- block count, but this is a documented infelicity.
                -- See NOTE on reordering corner cases.
                over _OldestFirst (Smg.<> blkZeroth) blockIndices
            ev =
                BlkEvApply $ BlockEventApply
                { _beaInput    = blockIndices'
                , _beaOutValid = BlockApplyFailure
                }
            gbes = GbesExpectedFailure
        return (Just ev, gbes)
    -- Succeed with or without rollback. Unfortunately, it's
    -- impossible to successfully rollback any blocks when
    -- there are no blocks, so we will generate a block apply
    -- event in both cases.
    genBlockStartingState (IsFailure False) (IsRollback _) = do
        blockIndices <- genBlockIndices "first"
        let
            ev = BlkEvApply $ BlockEventApply
                { _beaInput    = blockIndices
                , _beaOutValid = BlockApplySuccess
                }
            gbes = GbesBlockchain blockIndices
        return (Just ev, gbes)

    -- Fail with rollback.
    genBlockInBlockchain blockchain (IsFailure True) (IsRollback True) = do
        rft <- getRandom
        case rft of
            RftRollbackDrop -> do
                -- Attempt to rollback a part of the blockchain which
                -- is not its prefix (drop some blocks from the tip).
                -- The corner case here is that we may have a
                -- one-element blockchain: then we ensure failure by
                -- asking to rollback something entirely unrelated.
                case blockchain of
                    OldestFirst (_ :| []) -> do -- oops, the corner case
                        let
                            gbes = GbesExpectedFailure
                            ev = BlkEvRollback $ BlockEventRollback
                                { _berInput    = NewestFirst $ "unrelated" :| []
                                , _berOutValid = BlockRollbackFailure
                                }
                        return (Just ev, gbes)
                    _ -> do
                        -- Here we decide how many blocks to rollback.
                        -- This will yield a valid rollback, so we're
                        -- going to drop a single block from the tip.
                        -- Therefore, 'len' should be no less than 2,
                        -- otherwise we won't have a non-empty list
                        -- after the drop.
                        len <- getRandomR (2, length blockchain)
                        let
                            -- 'NE.fromList' is valid here because:
                            --    * the input has more than two elements
                            --    * 'len >= 2'
                            select = NE.fromList . drop 1 . NE.take len
                            blockIndices = toNewestFirst blockchain &
                                over _NewestFirst select
                            ev = BlkEvRollback $ BlockEventRollback
                                { _berInput    = blockIndices
                                , _berOutValid = BlockRollbackFailure
                                }
                            gbes = GbesExpectedFailure
                        return (Just ev, gbes)
    -- Fail without rollback (with apply).
    genBlockInBlockchain blockchain (IsFailure True) (IsRollback False) = do
        aft <- getRandom
        case aft of
            AftApplyBad -> do
                -- Attempt to apply an invalid sequence of blocks.
                let tip = NE.last (getOldestFirst blockchain)
                blockIndices <- genBlockIndices (tip <> "next")
                let
                    blockIndices' =
                        -- Those block indices are broken by construction
                        -- because we append the current tip to the end.
                        -- Sometimes we can violate the maximum bound on
                        -- block count, but this is a documented infelicity.
                        -- See NOTE on reordering corner cases.
                        over _OldestFirst (Smg.<> pure tip) blockIndices
                    ev = BlkEvApply $ BlockEventApply
                        { _beaInput    = blockIndices'
                        , _beaOutValid = BlockApplyFailure
                        }
                    gbes = GbesExpectedFailure
                return (Just ev, gbes)
            AftApplyNonCont -> do
                -- Attempt to apply blocks which are not a valid
                -- contuniation of our chain.
                let
                    tip  = NE.last (getOldestFirst blockchain)
                    -- The amount of blocks to skip. One is enough.
                    skip = (1 :: Int)
                blockIndices <- genBlockIndices (tip <> Smg.stimes (1+skip) "next")
                let
                    ev = BlkEvApply $ BlockEventApply
                        { _beaInput    = blockIndices
                        , _beaOutValid = BlockApplyFailure
                        }
                    gbes = GbesExpectedFailure
                return (Just ev, gbes)
    -- Success with rollback.
    genBlockInBlockchain blockchain (IsFailure False) (IsRollback True) = do
        len <- getRandomR (1, length blockchain)
        let
            (blockIndices, remainingBlockchain) = splitAtNewestFirst len $
                toNewestFirst blockchain
            -- 'NE.fromList' is valid here because 'len >= 1'.
            blockIndices' = over _NewestFirst NE.fromList blockIndices
            remainingBlockchain' = nonEmptyOldestFirst $
                toOldestFirst remainingBlockchain
            ev = BlkEvRollback $ BlockEventRollback
                { _berInput    = blockIndices'
                , _berOutValid = BlockRollbackSuccess
                }
            gbes = maybe GbesStartingState GbesBlockchain remainingBlockchain'
        return (Just ev, gbes)
    -- Success without rollback (with apply).
    genBlockInBlockchain blockchain (IsFailure False) (IsRollback False) = do
        let tip = NE.last (getOldestFirst blockchain)
        blockIndices <- genBlockIndices (tip <> "next")
        let
            ev = BlkEvApply $ BlockEventApply
                { _beaInput = blockIndices
                , _beaOutValid = BlockApplySuccess
                }
            gbes = GbesBlockchain (blockchain Smg.<> blockIndices)
        return (Just ev, gbes)

{- NOTE: Reordering corner cases
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When reordering blocks to get an invalid sequence, there's a corner case:
if there's only one block, it's impossible to get an invalid ordering.
The reason one might have only one block depends on the means of generation,
but for 'genBlockIndices' there are two possible causes:

* we rolled 'blockIndexEnd' equal to 'blockIndexStart'
* 'blockIndexMax' is 1

To avoid dealing with this, we append one more block. The downside is that
appending this block may cause the sequence to be longer than 'blockIndexMax'.

-}

newtype CheckCount = CheckCount Word
    deriving (Eq, Ord, Show, Num)

blkEvTip :: BlockEvent -> Maybe HeaderHash
blkEvTip = \case
    BlkEvApply bea -> Just $
        (headerHash . NE.head . getNewestFirst . toNewestFirst . view beaInput) bea
    BlkEvRollback ber -> Just $
        (headerHash . view prevBlockL . NE.head . getOldestFirst . toOldestFirst . view berInput) ber
    _ -> Nothing

-- | Empty: hash snapshot unavailable
--   Zero: hash snapshot available but unused
--   Other: hash snapshot was used N times
type HhStatusMap = Map HeaderHash CheckCount

hhSnapshotId :: HeaderHash -> SnapshotId
hhSnapshotId = SnapshotId . sformat hashHexF

-- | Whenever the resulting tips of apply/rollback operations coincide,
-- add a snapshot equivalence comparison.
enrichWithSnapshotChecking :: BlockScenario -> (BlockScenario, CheckCount)
enrichWithSnapshotChecking (BlockScenario bs) = (BlockScenario bs', checkCount)
  where
    checkCount = sum (hhStatusEnd :: HhStatusMap)
    (hhStatusEnd, revBs') = go Map.empty [] bs
    bs' = reverse revBs'
    -- NB. 'go' is tail-recursive.
    go hhStatusSoFar revNewBs = \case
        [] -> (hhStatusSoFar, revNewBs)
        (ev:evs) -> case blkEvTip ev of
            Nothing -> go hhStatusSoFar (ev:revNewBs) evs
            Just tipHh -> case Map.lookup tipHh hhStatusSoFar of
                Nothing ->
                    let
                        snapSave = BlkEvSnap (SnapshotSave (hhSnapshotId tipHh))
                        needSnapSave =
                            -- We tie the know here to determine whether to actually emit
                            -- the command to save the snapshot.
                            Map.findWithDefault 0 tipHh hhStatusEnd > 0
                        appendSnapSave = if needSnapSave then (snapSave:) else identity
                    in
                        go (Map.insert tipHh 0 hhStatusSoFar) (appendSnapSave $ ev:revNewBs) evs
                Just k ->
                    let snapEq = BlkEvSnap (SnapshotEq (hhSnapshotId tipHh))
                    in go (Map.insert tipHh (1+k) hhStatusSoFar) (snapEq:ev:revNewBs) evs
