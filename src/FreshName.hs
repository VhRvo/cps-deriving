module FreshName where

import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Text (Text)
import Data.Text qualified as Text
import System.IO.Unsafe (unsafePerformIO)

freshNameCounter :: IORef Int
freshNameCounter = unsafePerformIO (newIORef 0)
{-# NOINLINE freshNameCounter #-}

genFreshName :: () -> Text
genFreshName () = unsafePerformIO $ do
  nextId <- atomicModifyIORef' freshNameCounter $ \currentId ->
    let newId = currentId + 1
     in (newId, newId)
  pure (Text.pack ("$" ++ show nextId))
{-# NOINLINE genFreshName #-}
