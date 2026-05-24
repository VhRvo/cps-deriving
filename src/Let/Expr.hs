{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}
{-# Hlint ignore "Eta reduce" #-}
{-# Hlint ignore "Redundant lambda" #-}
{-# Hlint ignore "Redundant bracket" #-}
{-# Hlint ignore "Use id" #-}
{-# LANGUAGE OverloadedStrings #-}

module Let.Expr where

import Data.Text (Text)
import FreshName (genFreshName)

type Var = Text

data Expr
  = EVar Var
  | ELam Var Expr
  | EApp Expr Expr
  | If Expr Expr Expr
  | Let Var Expr Expr
  | Letrec Var Var Expr Expr
  | EConstant Int
  | EUnary UnaryOp Expr
  | EBinary BinaryOp Expr Expr
  | EFix Var Var Expr
  deriving (Show, Eq)

data UnaryOp = Negate
  deriving (Show, Eq)

data BinaryOp = Add | Subtract | Multiply | Divide
  deriving (Show, Eq)

reflect :: Expr -> Expr -> Expr
reflect k = \m -> EApp k m

reify :: (Expr -> Expr) -> Expr
reify f =
  let a = genFreshName "a"
   in ELam a (f (EVar a))
