-- Standalone check of the meta-continuation semantics `evalMK`
-- from meta-continuation-corrected.md, extended minimally with integer
-- constants and addition so we can OBSERVE answers. Run:  runghc CallccLeak.hs
--
-- Purpose: expose how `CallCC` interacts with `Reset` (undelimited,
-- meta-continuation-oblivious) versus how `Shift` does (delimited, composable).

module Main where

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  | Const Int
  | Add Expr Expr
  | Reset Expr
  | Shift String Expr
  | CallCC String Expr

data Value
  = VInt Int
  | VFun (Value -> Cont -> MCont -> Value)

type Cont  = Value -> MCont -> Value   -- value -> meta-continuation -> answer
type MCont = Value -> Value            -- value -> answer
type Env   = String -> Value

ext :: Env -> String -> Value -> Env
ext env x v = \y -> if y == x then v else env y

addV :: Value -> Value -> Value
addV (VInt a) (VInt b) = VInt (a + b)
addV _ _ = error "addV: non-integer"

apply :: Value -> Value -> Cont -> MCont -> Value
apply (VFun f) a k mk = f a k mk
apply _ _ _ _ = error "apply: non-function"

-- The six clauses, transcribed verbatim from the document
-- (plus Const and Add, which are pure/trivial like Var).
evalMK :: Env -> Expr -> Cont -> MCont -> Value
evalMK env (Var x) k mk =
  k (env x) mk
evalMK _   (Const n) k mk =
  k (VInt n) mk
evalMK env (Lam x body) k mk =
  k (VFun (\v k' mk' -> evalMK (ext env x v) body k' mk')) mk
evalMK env (App e1 e2) k mk =
  evalMK env e1
    (\f mk'  -> evalMK env e2
      (\a mk'' -> apply f a k mk'')
      mk')
    mk
evalMK env (Add e1 e2) k mk =
  evalMK env e1
    (\a mk'  -> evalMK env e2
      (\b mk'' -> k (addV a b) mk'')
      mk')
    mk
evalMK env (Reset body) k mk =
  evalMK env body
    (\x mk' -> mk' x)
    (\v -> k v mk)
evalMK env (Shift c body) k mk =
  evalMK (ext env c (VFun (\v k' mk' -> k v (\x -> k' x mk'))))
    body
    (\x mk'' -> mk'' x)
    mk
evalMK env (CallCC c body) k mk =
  evalMK (ext env c (VFun (\v k' mk' -> k v mk')))
    body
    k
    mk

run :: Expr -> Value
run e = evalMK env0 e (\v mk -> mk v) (\x -> x)
  where env0 = \x -> error ("unbound: " ++ x)

ppr :: Value -> String
ppr (VInt n) = show n
ppr (VFun _) = "<closure>"

-- Capture a continuation under outer Reset's "100 + []", then INVOKE it
-- from inside a DEEPER Reset whose context is "1 + []".
--
--   Reset (100 + OP "c" (Reset (1 + (c 5))))
--
-- Shift  : delimited/composable -> 100 + 5 + 1 = 106
-- CallCC : undelimited, mk-oblivious; the intervening Reset re-routes the
--          capture-point continuation, RE-applying "100 +" -> 205
example :: (String -> Expr -> Expr) -> Expr
example op =
  Reset
    (Add (Const 100)
         (op "c"
             (Reset (Add (Const 1)
                         (App (Var "c") (Const 5))))))

main :: IO ()
main = do
  putStrLn ("Shift  version: " ++ ppr (run (example Shift)))
  putStrLn ("CallCC version: " ++ ppr (run (example CallCC)))
