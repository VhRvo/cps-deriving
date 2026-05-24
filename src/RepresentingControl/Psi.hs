{-# LANGUAGE OverloadedStrings #-}

{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}
{-# Hlint ignore "Eta reduce" #-}
{-# Hlint ignore "Redundant lambda" #-}
{-# Hlint ignore "Redundant bracket" #-}
{-# Hlint ignore "Use id" #-}
{-# Hlint ignore "Move brackets to avoid $" #-}

module RepresentingControl.Psi where

import Data.Text (Text)
import Data.Text.IO qualified as T
import Expr
import FreshName (genFreshName)
import RepresentingControl.CpsConversion

data Value
  = VVar Var
  | VLam Var Expr

data NonValue
  = NApp Expr Expr

fromValue :: Value -> Expr
fromValue (VVar x) = EVar x
fromValue (VLam x e) = ELam x e

fromNonValue :: NonValue -> Expr
fromNonValue (NApp e1 e2) = EApp e1 e2

psi :: Value -> Expr
-- psi value = cpsC (fromValue value) (\x -> x)
psi (VVar x) =
  -- cpsC (fromValue (VVar x)) (\x -> x)
  -- cpsC (EVar x) (\x -> x)
  -- (\x -> x) (EVar x)
  (EVar x)
psi (VLam x e) =
  -- cpsC (fromValue (VLam x e)) (\x -> x)
  -- cpsC (ELam x e) (\x -> x)
  -- let k' = genFreshName "k"
  --  in (\x -> x) (ELam x (ELam k' ((cpsC' e) (EVar k'))))
  let k' = genFreshName "k"
   in (ELam x (ELam k' ((cpsC' e) (EVar k'))))

lemma11 :: Value -> (Expr -> Expr) -> Bool
-- lemma11 value k = cpsC (fromValue value) k == k (psi value)
lemma11 (VVar x) k =
  -- cpsC (fromValue (VVar x)) k == k (psi (VVar x))
  -- cpsC (EVar x) k == k (psi (VVar x))
  -- k (EVar x)      == k (psi (VVar x))
  k (EVar x) == k (EVar x)
lemma11 (VLam x e) k =
  -- cpsC (fromValue (VLam x e)) k == k (psi (VLam x e))
  -- cpsC (ELam x e) k == k (psi (VLam x e))
  -- (let k' = genFreshName "k" in k (ELam x (ELam k' (cpsC' e (EVar k')))))
  --   == (let k' = genFreshName "k" in (ELam x (ELam k' (cpsC' e (EVar k')))))
  True

lemma12 :: Value -> Expr -> Bool
-- lemma12 value dK = cpsC' (fromValue value) dK == EApp dK (psi value)
lemma12 (VVar x) dK =
  -- cpsC' (fromValue (VVar x)) dK == EApp dK (psi (VVar x))
  -- cpsC' (EVar x) dK == EApp dK (psi (VVar x))
  EApp dK (EVar x) == EApp dK (EVar x)
lemma12 (VLam x e) dK =
  -- cpsC' (fromValue (VLam x e)) dK == EApp dK (psi (VLam x e))
  -- cpsC' (ELam x e) dK == EApp dK (psi (VLam x e))
  -- (let k' = genFreshName "k" in EApp dK (ELam n (ELam k' (cpsC' e (EVar k')))))
  --   == EApp dK (psi (VLam x e))
  -- EApp dK (let k' = genFreshName "k" in (ELam n (ELam k' (cpsC' e (EVar k')))))
  --   == EApp dK (psi (VLam x e))
  EApp dK (let k' = genFreshName "k" in (ELam x (ELam k' (cpsC' e (EVar k')))))
    == EApp dK (let k' = genFreshName "k" in (ELam x (ELam k' ((cpsC' e) (EVar k')))))

lemma13 :: NonValue -> (Expr -> Expr) -> Bool
-- lemma13 nonValue k = cpsC (fromNonValue nonValue) k == cpsC' (fromNonValue nonValue) (reify k)
lemma13 (NApp e1 e2) k =
  -- cpsC (fromNonValue (NApp e1 e2)) k == cpsC' (fromNonValue (NApp e1 e2)) (reify k)
  -- cpsC (EApp e1 e2) k == cpsC' (EApp e1 e2) (reify k)
  (cpsC e1 $ \f -> cpsC e2 $ \arg -> EApp (EApp f arg) (reify k))
    == (cpsC e1 $ \f -> cpsC e2 $ \arg -> EApp (EApp f arg) (reify k))

-- another way
lemma13' :: NonValue -> (Expr -> Expr) -> Bool
-- lemma13' nonValue k = cpsC (fromNonValue nonValue) k == cpsC' (fromNonValue nonValue) (reify k)
lemma13' (NApp e1 e2) k =
  -- cpsC (fromNonValue (NApp e1 e2)) k == cpsC' (fromNonValue (NApp e1 e2)) (reify k)
  -- cpsC (EApp e1 e2) k == cpsC' (EApp e1 e2) (reify k)
  -- cpsC (EApp e1 e2) k == cpsC (EApp e1 e2) (reflect (reify k))
  cpsC (EApp e1 e2) k == cpsC (EApp e1 e2) k
