{-# LANGUAGE OverloadedStrings #-}

{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}
{-# Hlint ignore "Eta reduce" #-}

module Good.Conversion where

import Data.Text (Text)
import Data.Text.IO qualified as T
import Expr
import FreshName (genFreshName)

reflect :: Var -> Expr -> Expr
reflect k m = EApp (EVar k) m

reify :: (Expr -> Expr) -> Expr
reify f =
  let a = genFreshName "a"
   in ELam a (f (EVar a))

cpsC :: Expr -> (Expr -> Expr) -> Expr
cpsC (EVar n) k =
  k (EVar n)
cpsC (ELam n e) k =
  let k' = genFreshName "k"
   in --  in k (ELam n (ELam k' (cpsC e (\m -> EApp (EVar k') m))))
      k (ELam n (ELam k' (cpsC e (reflect k'))))
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      -- let a = genFreshName "a"
      --   in EApp (EApp f arg) (ELam a (k (EVar a)))
      EApp (EApp f arg) (reify k)

-- (@k (\f -> (\$k1 -> (@(@f x) (\$a2 -> (@$k1 $a2))))))
example1 :: IO ()
example1 = T.putStrLn $ prettyPrint $ cpsC (ELam "f" (EApp (EVar "f") (EVar "x"))) (\a -> EApp (EVar "k") a)

-- >>>
-- 1
