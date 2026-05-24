module Let.Rename where

import Let.Expr

-- | Rename free occurrences of the first variable to the second.
-- Precondition: the new variable is fresh for the whole expression.
renameFreeOccurrences :: Var -> Var -> Expr -> Expr
renameFreeOccurrences old new (EVar x)
  | x == old = EVar new
  | otherwise = EVar x
renameFreeOccurrences old new (ELam x e)
  | x == old = ELam x e
  | otherwise = ELam x (renameFreeOccurrences old new e)
renameFreeOccurrences old new (EApp e1 e2) = EApp (renameFreeOccurrences old new e1) (renameFreeOccurrences old new e2)
renameFreeOccurrences old new (If e1 e2 e3) =
  If
    (renameFreeOccurrences old new e1)
    (renameFreeOccurrences old new e2)
    (renameFreeOccurrences old new e3)
renameFreeOccurrences old new (Let x e1 e2)
  | x == old = Let x (renameFreeOccurrences old new e1) e2
  | otherwise = Let x (renameFreeOccurrences old new e1) (renameFreeOccurrences old new e2)
renameFreeOccurrences old new (Letrec f arg e1 e2) =
  -- Letrec f = \x. e1 in e2
  -- Let f = fix (\f x. e1) in e2
  Letrec f arg renamedFunctionBody renamedBody
  where
    renamedFunctionBody
      | f == old || arg == old = e1
      | otherwise = renameFreeOccurrences old new e1
    renamedBody
      | f == old = e2
      | otherwise = renameFreeOccurrences old new e2
renameFreeOccurrences _ _ (EConstant n) = EConstant n
renameFreeOccurrences old new (EUnary op e) = EUnary op (renameFreeOccurrences old new e)
renameFreeOccurrences old new (EBinary op e1 e2) = EBinary op (renameFreeOccurrences old new e1) (renameFreeOccurrences old new e2)
renameFreeOccurrences old new (EFix f arg e)
  | f == old || arg == old = EFix f arg e
  | otherwise = EFix f arg (renameFreeOccurrences old new e)
