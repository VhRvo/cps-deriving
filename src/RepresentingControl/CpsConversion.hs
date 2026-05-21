{-# LANGUAGE OverloadedStrings #-}

{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}
{-# Hlint ignore "Eta reduce" #-}
{-# Hlint ignore "Redundant lambda" #-}
{-# Hlint ignore "Redundant bracket" #-}

module RepresentingControl.CpsConversion where

import Data.Text (Text)
import Data.Text.IO qualified as T
import Expr
import FreshName (genFreshName)

reflect :: Expr -> Expr -> Expr
reflect k = \m -> EApp k m

reify :: (Expr -> Expr) -> Expr
reify f =
  let a = genFreshName "a"
   in ELam a (f (EVar a))

cpsC :: Expr -> (Expr -> Expr) -> Expr
cpsC (EVar x) k =
  k (EVar x)
cpsC (ELam x e) k =
  let k' = genFreshName "k"
   in k (ELam x (ELam k' (cpsC' e (EVar k'))))
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) (reify k)

cpsC' :: Expr -> Expr -> Expr
-- cpsC' expr k = cpsC expr (reflect k)
cpsC' (EVar n) k =
  EApp k (EVar n)
cpsC' (ELam n e) k =
  let k' = genFreshName "k"
   in EApp k (ELam n (ELam k' (cpsC' e (EVar k'))))
cpsC' (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) k
