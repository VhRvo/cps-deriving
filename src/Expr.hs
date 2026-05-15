module Expr where

import Data.Text (Text)

data Expr
  = EVar Text
  | ELam Text Expr
  | EApp Expr Expr
  deriving (Show, Eq)
