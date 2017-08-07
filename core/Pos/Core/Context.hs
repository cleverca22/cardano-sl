-- | Core runtime context.

module Pos.Core.Context
       ( CoreConstants (..)
       , HasCoreConstants
       , ccBlkSecuriryParam
       , blkSecurityParamM

       , HasPrimaryKey(..)
       , getOurSecretKey
       , getOurPublicKey
       , getOurKeys
       , getOurStakeholderId
       , getOurPubKeyAddress
       ) where

import           Universum

import           Control.Lens     (Getter, makeLenses)

import           Pos.Core.Address (addressHash, makePubKeyAddress)
import           Pos.Core.Types   (Address, BlockCount, StakeholderId)
import           Pos.Crypto       (PublicKey, SecretKey, toPublic)

-- | Core constants. They should be really constant and never change.
data CoreConstants = CoreConstants
    { _ccBlkSecuriryParam :: !BlockCount
    }

makeLenses ''CoreConstants

-- | Access to core constants. The access is read-only to ensure that
-- the constants are really constants (i. e. can't be changed).
class HasCoreConstants ctx where
    coreConstantsG :: Getter ctx CoreConstants

blkSecurityParamM :: (HasCoreConstants ctx, MonadReader ctx m) => m BlockCount
blkSecurityParamM = view (coreConstantsG . ccBlkSecuriryParam)

-- | Access to primary key of the node.
class HasPrimaryKey ctx where
    primaryKey :: Lens' ctx SecretKey

getOurSecretKey :: (MonadReader ctx m, HasPrimaryKey ctx) => m SecretKey
getOurSecretKey = view primaryKey

getOurPublicKey :: (MonadReader ctx m, HasPrimaryKey ctx) => m PublicKey
getOurPublicKey = toPublic <$> getOurSecretKey

getOurKeys :: (MonadReader ctx m, HasPrimaryKey ctx) => m (SecretKey, PublicKey)
getOurKeys = (identity &&& toPublic) <$> getOurSecretKey

getOurStakeholderId :: (MonadReader ctx m, HasPrimaryKey ctx) => m StakeholderId
getOurStakeholderId = addressHash <$> getOurPublicKey

getOurPubKeyAddress :: (MonadReader ctx m, HasPrimaryKey ctx) => m Address
getOurPubKeyAddress = makePubKeyAddress <$> getOurPublicKey
