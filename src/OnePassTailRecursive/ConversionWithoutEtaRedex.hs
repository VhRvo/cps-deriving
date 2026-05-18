{-# LANGUAGE OverloadedStrings #-}

{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}

module OnePassTailRecursive.ConversionWithoutEtaRedex where

import Data.Text (Text)
import Data.Text.IO qualified as T
import Expr
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

cpsC' :: Expr -> Expr -> Expr
cpsC' (EVar n) k =
  EApp k (EVar n)
cpsC' (ELam n e) k =
  let k' = genFreshName "k"
   in EApp k (ELam n (ELam k' (cpsC' e (EVar k'))))
cpsC' (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) k

-- (@topK (\f -> (\$k1 -> (@(@f x) $k1))))
e1 :: IO ()
e1 = T.putStrLn $ prettyPrint $ cpsC' (ELam "f" (EApp (EVar "f") (EVar "x"))) (EVar "topK")

-- (@topK (\f -> (\$k2 -> (@(@f x) (\$a3 -> (@(@$a3 x) $k2))))))
e2 :: IO ()
e2 =
  T.putStrLn $
    prettyPrint $
      cpsC' (ELam "f" (EApp (EApp (EVar "f") (EVar "x")) (EVar "x"))) (EVar "topK")

-- >>>
-- 1
