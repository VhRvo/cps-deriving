{-# LANGUAGE OverloadedStrings #-}

module Expr where

import Data.Text (Text)

data Expr
  = EVar Text
  | ELam Text Expr
  | EApp Expr Expr
  deriving (Show, Eq)

prettyPrint :: Expr -> Text
prettyPrint (EVar n) = n
prettyPrint (ELam n e) = "(\\" <> n <> " -> " <> prettyPrint e <> ")"
prettyPrint (EApp e1 e2) = "(@" <> prettyPrint e1 <> " " <> prettyPrint e2 <> ")"
