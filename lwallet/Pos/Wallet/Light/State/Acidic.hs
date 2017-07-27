{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Pos.Wallet.Light.State.Acidic
       (
         WalletState
       , closeState
       , openMemState
       , openState
       , query
       , tidyState
       , update

       , GetBlock (..)
       , GetBestChain (..)

       , GetUtxo (..)
       , GetOldestUtxo (..)
       , GetTxHistory (..)
       ) where

import           Universum

import           Data.Acid                      (EventResult, EventState, QueryEvent,
                                                 UpdateEvent, makeAcidic)
import           Serokell.AcidState             (ExtendedState, closeExtendedState,
                                                 openLocalExtendedState,
                                                 openMemoryExtendedState, queryExtended,
                                                 tidyExtendedState, updateExtended)

import           Pos.Txp                        (GenesisUtxo)

import           Pos.Wallet.Light.State.Storage (Storage)
import           Pos.Wallet.Light.State.Storage as WS

type WalletState = ExtendedState Storage

query
    :: (EventState event ~ Storage, QueryEvent event, MonadIO m)
    => WalletState -> event -> m (EventResult event)
query = queryExtended

update
    :: (EventState event ~ Storage, UpdateEvent event, MonadIO m)
    => WalletState -> event -> m (EventResult event)
update = updateExtended

openState :: MonadIO m => Bool -> GenesisUtxo -> FilePath -> m WalletState
openState deleteIfExists genUtxo fp =
    openLocalExtendedState deleteIfExists fp $ WS.mkStorage genUtxo

openMemState :: MonadIO m => GenesisUtxo -> m WalletState
openMemState = openMemoryExtendedState . WS.mkStorage

closeState :: MonadIO m => WalletState -> m ()
closeState = closeExtendedState

tidyState :: MonadIO m => WalletState -> m ()
tidyState = tidyExtendedState

makeAcidic ''Storage
    [
      'WS.getBlock
    , 'WS.getBestChain
    , 'WS.getUtxo
    , 'WS.getOldestUtxo
    , 'WS.getTxHistory
    ]
