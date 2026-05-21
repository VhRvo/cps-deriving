{-# LANGUAGE OverloadedStrings #-}

{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}

module Good.DerivingBetter where

import Data.Text (Text)
import Data.Text.IO qualified as T
import Expr
import FreshName (genFreshName)

cpsC :: Expr -> (Expr -> Expr) -> Expr
cpsC (EVar n) k =
  k (EVar n)
cpsC (ELam n e) k =
  -- let k' = genFreshName "k"
  --  in k (ELam n (ELam k' (cpsC e (\m -> EApp (EVar k') m))))
  let k' = genFreshName "k"
   in k (ELam n (ELam k' (cpsC' e k')))
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      let a = genFreshName "a"
       in EApp (EApp f arg) (ELam a (k (EVar a)))

-- (@k (\f -> (\$k1 -> (@(@f x) (\$a2 -> (@$k1 $a2))))))
example1 :: IO ()
example1 = T.putStrLn $ prettyPrint $ cpsC (ELam "f" (EApp (EVar "f") (EVar "x"))) (\a -> EApp (EVar "k") a)

-- >>>
-- 1

cpsC' :: Expr -> Var -> Expr
-- cpsC' expr k = cpsC expr (\e -> EApp (EVar k) e)
cpsC' (EVar n) k =
  -- cpsC (EVar n) (\e -> EApp (EVar k) e)
  -- (\e -> EApp (EVar k) e) (EVar n)
  EApp (EVar k) (EVar n)
cpsC' (ELam n e) k =
  -- cpsC (ELam n e) (\e -> EApp (EVar k) e)
  -- let k' = genFreshName "k"
  --  in (\e -> EApp (EVar k) e) (ELam n (ELam k' (cpsC e (\m -> EApp (EVar k') m))))
  -- let k' = genFreshName "k"
  --  in EApp (EVar k) (ELam n (ELam k' (cpsC e (\m -> EApp (EVar k') m))))
  let k' = genFreshName "k"
   in EApp (EVar k) (ELam n (ELam k' (cpsC' e k')))
cpsC' (EApp e1 e2) k =
  -- cpsC (EApp e1 e2) (\e -> EApp (EVar k) e)
  -- cpsC e1 $ \f ->
  --   cpsC e2 $ \arg ->
  --     let a = genFreshName "a"
  --      in EApp (EApp f arg) (ELam a ((\e -> EApp (EVar k) e) (EVar a)))
  -- cpsC e1 $ \f ->
  --   cpsC e2 $ \arg ->
  --     let a = genFreshName "a"
  --      in EApp (EApp f arg) (ELam a (EApp (EVar k) (EVar a)))
  -- cpsC e1 $ \f ->
  --   cpsC e2 $ \arg ->
  --     let a = genFreshName "a"
  --      in EApp (EApp f arg) (EVar k)
  {- eta-reduction -}
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) (EVar k)
