{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -fno-warn-unused-top-binds #-} -- for lenses

-- | Parameters for launching everything.

module Pos.Launcher.Param
       ( LoggingParams (..)
       , BaseParams (..)
       , TransportParams (..)
       , NodeParams (..)
       ) where

import           Universum

import           Control.Lens            (makeLensesWith)
import           Ether.Internal          (HasLens (..))
import qualified Network.Transport.TCP   as TCP
import           System.Wlog             (LoggerName)

import           Pos.Core                (HasPrimaryKey (..), Timestamp)
import           Pos.Crypto              (SecretKey)
import           Pos.DHT.Real.Param      (KademliaParams)
import           Pos.Network.Types       (NetworkConfig)
import           Pos.Reporting.MemState  (HasReportServers (..))
import           Pos.Security.Params     (SecurityParams)
import           Pos.Statistics          (EkgParams, StatsdParams)
import           Pos.Txp.Toil.Types      (GenesisStakeholders, GenesisTxpContext,
                                          GenesisUtxo, gtcStakeholders, gtcUtxo)
import           Pos.Update.Params       (UpdateParams)
import           Pos.Util.UserSecret     (UserSecret)
import           Pos.Util.Util           (postfixLFields)

-- | Contains all parameters required for hierarchical logger initialization.
data LoggingParams = LoggingParams
    { lpRunnerTag     :: !LoggerName        -- ^ Prefix for logger, like "time-slave"
    , lpHandlerPrefix :: !(Maybe FilePath)  -- ^ Prefix of path for all logs
    , lpConfigPath    :: !(Maybe FilePath)  -- ^ Path to logger configuration
    } deriving (Show)

-- | Contains basic & networking parameters for running node.
data BaseParams = BaseParams
    { bpLoggingParams   :: !LoggingParams  -- ^ Logger parameters
    } deriving (Show)

-- | Network parameters.
data TransportParams = TransportParams
    { tpTcpAddr   :: !TCP.TCPAddr
    -- ^ External TCP address of the node.
    -- It encapsulates bind address and address visible to other nodes.
    }

-- | This data type contains all data necessary to launch node and
-- known in advance (from CLI, configs, etc.)
data NodeParams = NodeParams
    { npDbPathM        :: !FilePath             -- ^ Path to node's database
    , npRebuildDb      :: !Bool                 -- ^ @True@ if data-base should be rebuilt
    , npSystemStart    :: !Timestamp            -- ^ System start
    , npSecretKey      :: !SecretKey            -- ^ Primary secret key of node
    , npUserSecret     :: !UserSecret           -- ^ All node secret keys
    , npBaseParams     :: !BaseParams           -- ^ See 'BaseParams'
    , npGenesisTxpCtx  :: !GenesisTxpContext    -- ^ Predefined genesis context related to txp data.
    , npJLFile         :: !(Maybe FilePath)     -- TODO COMMENT
    , npPropagation    :: !Bool                 -- ^ Whether to propagate txs, ssc data, blocks to neighbors
    , npReportServers  :: ![Text]               -- ^ List of report server URLs
    , npUpdateParams   :: !UpdateParams         -- ^ Params for update system
    , npSecurityParams :: !SecurityParams       -- ^ Params for "Pos.Security"
    , npUseNTP         :: !Bool                 -- ^ Whether to use synchronisation with NTP servers.
    , npTransport      :: !TransportParams      -- ^ (TCP) transport parameters.
    , npEnableMetrics  :: !Bool                 -- ^ Gather runtime statistics.
    , npEkgParams      :: !(Maybe EkgParams)    -- ^ EKG statistics monitoring.
    , npStatsdParams   :: !(Maybe StatsdParams) -- ^ statsd statistics backend.
    , npNetworkConfig  :: !(NetworkConfig KademliaParams)
    } -- deriving (Show)

makeLensesWith postfixLFields ''NodeParams

instance HasLens UpdateParams NodeParams UpdateParams where
    lensOf = npUpdateParams_L

instance HasLens SecurityParams NodeParams SecurityParams where
    lensOf = npSecurityParams_L

instance HasLens GenesisTxpContext NodeParams GenesisTxpContext where
    lensOf = npGenesisTxpCtx_L

instance HasLens GenesisUtxo NodeParams GenesisUtxo where
    lensOf = npGenesisTxpCtx_L . gtcUtxo

instance HasLens GenesisStakeholders NodeParams GenesisStakeholders where
    lensOf = npGenesisTxpCtx_L . gtcStakeholders

instance HasLens (NetworkConfig KademliaParams) NodeParams (NetworkConfig KademliaParams) where
    lensOf = npNetworkConfig_L

instance HasReportServers NodeParams where
    reportServers = npReportServers_L

instance HasPrimaryKey NodeParams where
    primaryKey = npSecretKey_L
