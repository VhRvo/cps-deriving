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

type Var = Text

reflect :: Var -> Expr -> Expr
reflect k = \m -> EApp (EVar k) m

reify :: (Expr -> Expr) -> Expr
reify f =
  let a = genFreshName "a"
   in ELam a (f (EVar a))

cpsC :: Expr -> (Expr -> Expr) -> Expr
cpsC (EVar n) k =
  k (EVar n)
cpsC (ELam n e) k =
  let k' = genFreshName "k"
   in --  in k (ELam n (ELam k' (cpsC e (reflect k'))))
      k (ELam n (ELam k' (cpsC' e k')))
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) (reify k)

-- (@k (\f -> (\$k1 -> (@(@f x) (\$a2 -> (@$k1 $a2))))))
example1 :: IO ()
example1 = T.putStrLn $ prettyPrint $ cpsC (ELam "f" (EApp (EVar "f") (EVar "x"))) (\a -> EApp (EVar "k") a)

-- >>>
-- 1

cpsC' :: Expr -> Var -> Expr
-- cpsC' expr k = cpsC expr (reflect k)
cpsC' (EVar n) k =
  -- cpsC (EVar n) (reflect k)
  -- (reflect k) (EVar n)
  -- (\m -> EApp (EVar k) m) (EVar n)
  EApp (EVar k) (EVar n)
cpsC' (ELam n e) k =
  -- cpsC (ELam n e) (reflect k)
  -- let k' = genFreshName "k"
  --  in (reflect k) (ELam n (ELam k' (cpsC e (reflect k'))))
  -- let k' = genFreshName "k"
  --  in (\m -> EApp (EVar k) m) (ELam n (ELam k' (cpsC e (reflect k'))))
  -- let k' = genFreshName "k"
  --  in EApp (EVar k) (ELam n (ELam k' (cpsC e (reflect k'))))
  let k' = genFreshName "k"
   in EApp (EVar k) (ELam n (ELam k' (cpsC' e k')))
cpsC' (EApp e1 e2) k =
  -- cpsC (EApp e1 e2) (reflect k)
  -- cpsC e1 $ \f ->
  --   cpsC e2 $ \arg ->
  --     EApp (EApp f arg)
  --       (reify (reflect k))
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) (EVar k)

reflectAfterReify :: Var -> Expr
reflectAfterReify k =
  -- reify (reflect k)
  -- let a = genFreshName "a"
  --  in ELam a ((reflect k) (EVar a))
  -- let a = genFreshName "a"
  --  in ELam a ((\m -> EApp (EVar k) m) (EVar a))
  -- let a = genFreshName "a"
  --  in ELam a (EApp (EVar k) (EVar a))
  {- eta-reduction -}
  EVar k
