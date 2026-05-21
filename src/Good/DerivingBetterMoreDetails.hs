{-# LANGUAGE OverloadedStrings #-}

{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}
{-# Hlint ignore "Eta reduce" #-}
{-# Hlint ignore "Redundant lambda" #-}
{-# Hlint ignore "Redundant bracket" #-}

module Good.DerivingBetterMoreDetails where

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
cpsC (EVar n) k =
  k (EVar n)
cpsC (ELam n e) k =
  let k' = genFreshName "k"
   in -- k (ELam n (ELam k' (cpsC e (reflect (EVar k')))))
      k (ELam n (ELam k' (cpsC' e (EVar k'))))
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) (reify k)

-- (@k (\f -> (\$k1 -> (@(@f x) (\$a2 -> (@$k1 $a2))))))
example1 :: IO ()
example1 = T.putStrLn $ prettyPrint $ cpsC (ELam "f" (EApp (EVar "f") (EVar "x"))) (\a -> EApp (EVar "k") a)

-- >>>
-- 1

cpsC' :: Expr -> Expr -> Expr
cpsC' expr k = cpsC expr (reflect k)
cpsC' (EVar n) k =
  -- cpsC (EVar n) (reflect k)
  -- (reflect k) (EVar n)
  -- (\m -> EApp k m) (EVar n)
  EApp k (EVar n)
cpsC' (ELam n e) k =
  -- cpsC (ELam n e) (reflect (k)
  -- let k' = genFreshName "k"
  --  in (reflect k) (ELam n (ELam k' (cpsC e (reflect k'))))
  -- let k' = genFreshName "k"
  --  in (\m -> EApp (EVar k) m) (ELam n (ELam k' (cpsC e (reflect k'))))
  -- let k' = genFreshName "k"
  --  in EApp (EVar k) (ELam n (ELam k' (cpsC e (reflect k'))))
  let k' = genFreshName "k"
   in EApp k (ELam n (ELam k' (cpsC' e (EVar k'))))
cpsC' (EApp e1 e2) k =
  -- cpsC (EApp e1 e2) (reflect k)
  -- cpsC e1 $ \f ->
  --   cpsC e2 $ \arg ->
  --     EApp (EApp f arg)
  --       (reify (reflect k))
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) k

reifyAfterReflect :: Expr -> Bool
reifyAfterReflect k =
  -- reify (reflect k) == k
  -- (let a = genFreshName "a" in ELam a ((reflect k) (EVar a))) == k
  -- (let a = genFreshName "a" in ELam a ((reflect k) (EVar a))) == k
  -- (let a = genFreshName "a" in ELam a ((\m -> EApp (EVar k) m) (EVar a))) == k
  -- (let a = genFreshName "a" in ELam a (EApp (EVar k) (EVar a))) == k
  -- {- eta-reduction -}
  k == k

reflectAfterReify :: (Expr -> Expr) -> Expr -> Bool
reflectAfterReify k m =
  -- The difficult direction is not a literal Haskell equality between functions.
  -- `k` is a meta-level function, so Haskell cannot inspect it as an object-language term,
  -- and arbitrary functions of type `Expr -> Expr` may observe the exact syntax of their input.
  --
  -- What we want is the object-language beta law, for context-like static continuations:
  --   reflect (reify k) m
  --   = EApp (ELam a (k (EVar a))) m
  --   =={ object-language beta }
  --   k m
  --
  -- Function extensionality then says that `reflect (reify k)` and `k` are the same
  -- continuation, but only up to object-language beta-equivalence and only for
  -- well-behaved syntactic contexts, not for every possible Haskell function.
  -- k m == reflect (reify k) m
  -- k m == (\m -> EApp (reify k) m) m
  -- k m == EApp (reify k) m
  -- k m == EApp (let a = genFreshName "a" in ELam a (k (EVar a))) m
  k m == k m
