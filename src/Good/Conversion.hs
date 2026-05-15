{-# LANGUAGE OverloadedStrings #-}

{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}

module Good.Conversion where

import Expr
import Data.Text (Text)
import Data.Text.IO qualified as T
import FreshName (genFreshName)

cpsC :: Expr -> (Expr -> Expr) -> Expr
cpsC (EVar n) k =
  k (EVar n)
cpsC (ELam n e) k =
  let k' = genFreshName "k"
   in k (ELam n (ELam k' (cpsC e (\m -> EApp (EVar k') m))))
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      let a = genFreshName "a"
       in EApp (EApp f arg) (ELam a (k (EVar a)))

-- (@k (\f -> (\$k1 -> (@(@f x) (\$a2 -> (@$k1 $a2))))))
e1 :: IO ()
e1 = T.putStrLn $ prettyPrint $ cpsC (ELam "f" (EApp (EVar "f") (EVar "x"))) (\a -> EApp (EVar "k") a)

-- >>>
-- 1

