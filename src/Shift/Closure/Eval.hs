{-# Hlint ignore "Use camelCase" #-}
{-# Hlint ignore "Use lambda-case" #-}
{-# Hlint ignore "Avoid lambda" #-}
{-# Hlint ignore "Eta reduce" #-}
{-# Hlint ignore "Redundant lambda" #-}
{-# Hlint ignore "Redundant bracket" #-}
{-# Hlint ignore "Use id" #-}
{-# Hlint ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE OverloadedStrings #-}

module Shift.Closure.Eval where

import Data.Map (Map, (!))
import qualified Data.Map as Map
import Shift.Expr

{-
data Expr
  = EVar Var
  | ELam Var Expr
  | EApp Expr Expr
  | EIf Expr Expr Expr
--   | Let Var Expr Expr
--   | Letrec Var Var Expr Expr
  | EConstant Int
  | EUnary UnaryOp Expr
  | EBinary BinaryOp Expr Expr
--   | EFix Var Var Expr
-}

type Env = Map Var Value

data Value
  = VClosure Env Var Expr
  | VInt Int

eval :: Env -> Expr -> Value
eval env expr =
  case expr of
    EVar var -> env ! var
    ELam para body -> VClosure env para body
    EIf test conseq alter ->
      case eval env test of
        VInt n | n /= 0 -> eval env conseq
        _ -> eval env alter
    EConstant int -> VInt int
    EUnary op rhs -> undefined
    EBinary op lhs rhs -> undefined
    EShift var body -> undefined
    EReset body -> undefined

evalK :: Env -> Expr -> (Value -> Value) -> Value
-- evalK env expr k = k (eval env expr)
evalK env expr k =
  case expr of
    EVar var -> k (env ! var)
    ELam para body -> k (VClosure env para body)
    EIf test conseq alter ->
      evalK env test $ \v ->
        case v of
          VInt n | n /= 0 -> evalK env conseq k
          _ -> evalK env alter k
    EConstant int -> k (VInt int)
    EUnary op rhs -> undefined
    EBinary op lhs rhs -> undefined
    EShift var body -> evalK (Map.insert var undefined env) body (\x -> x)
    EReset body -> evalK env body (\x -> x)

type MCont = Value -> Value

evalMK :: Env -> Expr -> (Value -> (Value -> Value) -> Value) -> (Value -> Value) -> Value
-- evalMK env expr k mk = mk (k (eval env expr))
-- evalMK env expr k mk = k (eval env expr) mk
-- ? evalMK env expr k mk = evalK env expr (\v -> k v mk): wrong
evalMK env expr k mk =
  case expr of
    EVar var -> k (env ! var) mk
    ELam para body -> k (VClosure env para body) mk
    EIf test conseq alter ->
      --   k
      --     ( case eval env test of
      --         VInt n | n /= 0 -> eval env conseq
      --         _ -> eval env alter
      --     )
      --     mk
      {- => -}
      --   ( \value ->
      --       k
      --         ( case value of
      --             VInt n | n /= 0 -> eval env conseq
      --             _ -> eval env alter
      --         )
      --   )
      --     (eval env test)
      --     mk
      {- => -}
    --   evalMK
    --     env
    --     test
    --     ( \value ->
    --         k
    --           ( case value of
    --               VInt n | n /= 0 -> eval env conseq
    --               _ -> eval env alter
    --           )
    --     )
    --     mk
      {- =eta> -}
      evalMK
        env
        test
        ( \value mk' ->
            k
              ( case value of
                  VInt n | n /= 0 -> eval env conseq
                  _ -> eval env alter
              )
              mk'
        )
        mk
    EConstant int -> k (VInt int) mk
    EUnary op rhs -> undefined
    EBinary op lhs rhs -> undefined
