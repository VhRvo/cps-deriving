{-# LANGUAGE OverloadedStrings #-}

module Expr where

import Data.Text (Text)

type Var = Text

data Expr
  = EVar Var
  | ELam Var Expr
  | EApp Expr Expr
  deriving (Show, Eq)

prettyPrint :: Expr -> Text
prettyPrint (EVar n) = n
prettyPrint (ELam n e) = "(\\" <> n <> " -> " <> prettyPrint e <> ")"
prettyPrint (EApp e1 e2) = "(@" <> prettyPrint e1 <> " " <> prettyPrint e2 <> ")"
