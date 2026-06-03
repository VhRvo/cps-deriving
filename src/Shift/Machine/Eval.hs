{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- A first-order abstract machine for shift/reset, obtained by
-- /defunctionalizing/ the meta-continuation semantics @evalMK@
-- (see "Shift.Closure.Eval").
--
-- Two function spaces are turned into first-order data:
--
--   * @Cont = Value -> MCont -> Ans@   becomes the datatype 'K'
--     (the control stack / current delimited continuation);
--   * @MCont = Value -> Ans@           becomes the datatype 'C'
--     (the meta-control stack / chain of enclosing contexts).
--
-- The two interpreters 'applyK' and 'applyC' are the apply functions of
-- the defunctionalization; 'eval' is the defunctionalized @evalMK@.
--
-- Correctness (refunctionalization): writing @|.|@ for the obvious
-- "refunctionalize" maps
--
--   @|K| : K -> (Value -> (Value -> Value) -> Value)@,
--   @|C| : C -> (Value -> Value)@,
--
-- one has, by induction on the call structure,
--
--   @applyK k v c   = |K| k v |C| c@
--   @applyC c v     = |C| c v@
--   @eval env e k c = evalMK env e |K| k |C| c@
--
-- so @run = top-level evalMK with identity continuation and identity
-- meta-continuation@.
module Shift.Machine.Eval where

import Data.Map (Map)
import qualified Data.Map as Map
import Shift.Expr

type Env = Map Var Value

-- | The answer type is just 'Value' (the machine returns a final value).
data Value
  = VInt Int
  | VClosure Env Var Expr
  | -- | A delimited continuation reified by 'EShift' (a first-class value).
    VCont K
  deriving (Show)

-- | Defunctionalized continuations: @Value -> MCont -> Ans@.
data K
  = -- | The identity continuation @iota = \\x g -> g x@.
    KEmpty
  | -- | Operator being evaluated; remember operand, env and outer continuation.
    KApp1 Env Expr K
  | -- | Operator value known; operand being evaluated.
    KApp2 Value K
  | -- | Test being evaluated; remember both branches.
    KIf Env Expr Expr K
  | KUnary UnaryOp K
  | KBinary1 Env BinaryOp Expr K
  | KBinary2 Value BinaryOp K
  deriving (Show)

-- | Defunctionalized meta-continuations: @Value -> Ans@.
data C
  = -- | Top-level meta-continuation @\\x -> x@.
    CHalt
  | -- | @reset@ frame: @\\v -> applyK k v c@   (= @C_reset k c@).
    CReset K C
  | -- | @shift@ call frame: @\\w -> applyK k w c@ (= @C_shift k c@).
    CShift K C
  deriving (Show)

-- | Interpret a continuation: the apply function of the @Cont@ defunctionalization.
applyK :: K -> Value -> C -> Value
applyK KEmpty x c = applyC c x
applyK (KApp1 env e2 k) f c = eval env e2 (KApp2 f k) c
applyK (KApp2 f k) a c = applyProc f a k c
applyK (KIf env e1 e2 k) v c =
  case v of
    VInt n | n /= 0 -> eval env e1 k c
    _ -> eval env e2 k c
applyK (KUnary Negate k) v c =
  case v of
    VInt n -> applyK k (VInt (negate n)) c
    _ -> error "applyK: Negate of a non-integer"
applyK (KBinary1 env op e2 k) v1 c = eval env e2 (KBinary2 v1 op k) c
applyK (KBinary2 v1 op k) v2 c = applyK k (binop op v1 v2) c

-- | Interpret a meta-continuation: the apply function of the @MCont@ defunctionalization.
applyC :: C -> Value -> Value
applyC CHalt x = x
applyC (CReset k c) v = applyK k v c
applyC (CShift k c) w = applyK k w c

-- | Apply a procedure value.
applyProc :: Value -> Value -> K -> C -> Value
applyProc (VClosure env x body) v k c = eval (Map.insert x v env) body k c
-- A reified continuation, when applied, pushes the /current/ (k, c) as a new
-- shift frame and resumes the captured continuation @k0@.  This mirrors
-- @p_mc = \\v k' g' -> k v (\\w -> k' w g')@ from the MCS.
applyProc (VCont k0) v k c = applyK k0 v (CShift k c)
applyProc (VInt _) _ _ _ = error "applyProc: applied a non-procedure"

-- | The defunctionalized @evalMK@.
eval :: Env -> Expr -> K -> C -> Value
eval env e k c =
  case e of
    EVar x -> applyK k (env Map.! x) c
    EConstant n -> applyK k (VInt n) c
    ELam x body -> applyK k (VClosure env x body) c
    EApp e1 e2 -> eval env e1 (KApp1 env e2 k) c
    EIf t a b -> eval env t (KIf env a b k) c
    EUnary op r -> eval env r (KUnary op k) c
    EBinary op l r -> eval env l (KBinary1 env op r k) c
    -- shift: capture @k@ as a value, reset the continuation to identity.
    EShift x body -> eval (Map.insert x (VCont k) env) body KEmpty c
    -- reset: push @(k, c)@ as a delimiter and start with identity continuation.
    EReset body -> eval env body KEmpty (CReset k c)

binop :: BinaryOp -> Value -> Value -> Value
binop op (VInt a) (VInt b) =
  VInt $ case op of
    Add -> a + b
    Subtract -> a - b
    Multiply -> a * b
    Divide -> a `div` b
binop _ _ _ = error "binop: non-integer operand"

-- | Run a closed term on the machine with the empty environment, identity
-- continuation and the halting meta-continuation.
run :: Expr -> Value
run e = eval Map.empty e KEmpty CHalt

-- | Example:  @1 + reset (10 + shift k. 100)@  ==>  @101@
-- (the @+10@ inside the delimiter is discarded by @shift@, the @+1@ outside is not).
example :: Value
example =
  run $
    EBinary
      Add
      (EConstant 1)
      ( EReset
          ( EBinary
              Add
              (EConstant 10)
              (EShift "k" (EConstant 100))
          )
      )
