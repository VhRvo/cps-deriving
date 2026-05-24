{-# LANGUAGE OverloadedStrings #-}

module Let.Conversion where

import FreshName (genFreshName)
import Let.Expr
import Let.Rename (renameFreeOccurrences)

fix :: Expr
fix = EVar "fix"

-- Bad route: treating fix as an ordinary lambda value loses the real shape of
-- the recursive knot.
--
-- fix f = f (fix f)
--   [ fix ]
-- = [\f. f (fix f) ]
-- = \f_k k. [ f (fix f) ] k
-- = \f_k k. [f] $ \f_k -> [ fix f ] $ \app -> f_k app k
-- = \f_k k. [ fix f ] $ \app -> f_k app k
-- = \f_k k. [ fix ] $ \fix_k -> [ f ] $ \f_k -> fix_k f_k (\app -> f_k app k)
-- = \f_k k. [ f ] $ \f_k -> fix_k f_k (\app -> f_k app k)
-- = \f_k k. fix_k f_k (\app -> f_k app k)
--
-- Better route: keep Fix as the primitive recursive knot, and only observe its
-- equational behavior.
--
-- Fix f = f (Fix f)
-- FixF f k = f (Fix f) k
--
-- So FixF is not a second, independent definition. It is the CPS eta-expansion
-- of the same knot: the recursive value now accepts the ordinary argument and
-- then a dynamic continuation.
--
-- For comparison, if we eta-expand the usual recursive function equation before
-- CPS, we get the same intuition:
--
-- fix f = f (\x . fix f x)
-- fix_k
-- = [ fix ] (\x. x)
-- = [ \f. f (\x. fix f x) ] (\x. x)
-- = (\x. x) (\f k. [ f (\x. fix f x) ] k)
-- = \f k. [ f (\x. fix f x) ] k
--
-- In the syntax below this idea is represented by EFix, a value constructor that
-- binds the recursive knot. EFix is therefore closer to ELam than to EApp.

fixF :: Expr
fixF = EVar "fixF"

cpsC :: Expr -> (Expr -> Expr) -> Expr
cpsC (EVar x) k =
  k (EVar x)
cpsC (ELam x e) k =
  let k' = genFreshName "k"
   in k (ELam x (ELam k' (cpsC e (reflect (EVar k')))))
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      EApp (EApp f arg) (reify k)
cpsC (If e1 e2 e3) k =
  cpsC e1 $ \cond ->
    If
      cond
      (cpsC e2 k)
      (cpsC e3 k)
cpsC (Let x e1 e2) k =
  -- Let x e1 e2 := (ELam x e2) e1
  --
  -- Step labels:
  --   =meta>   expand cpsC / apply meta-level continuations
  --   =alpha>  object-language alpha-renaming
  --   =beta>   object-language beta reduction
  --   =admin>  administrative let rearrangement
  --   =eta>    reflect/reify eta reduction
  --
  -- cpsC (EApp (ELam x e2) e1) k
  -- =meta>
  -- cpsC (ELam x e2) $ \fun ->
  --   cpsC e1 $ \value ->
  --     EApp (EApp fun value) (reify k)
  -- =meta>
  --  cpsC e1 $ \value ->
  --    let k' = genFreshName "k"
  --     in EApp
  --          (EApp (ELam x (ELam k' (cpsC e2 (reflect (EVar k'))))) value)
  --           -- reify f = let a = genFreshName "a" in ELam a (f (EVar a))
  --          (reify k)
  -- =alpha>  choosing x' fresh for value, e2, and reify k
  --  cpsC e1 $ \value ->
  --    let x' = genFreshName x
  --        k' = genFreshName "k"
  --     in EApp
  --          (EApp (ELam x' (ELam k' (cpsC (renameFreeOccurrences x x' e2) (reflect (EVar k'))))) value)
  --          (reify k)
  -- =beta>  turn the object-level lambda application into a let binding
  --   cpsC e1 $ \value ->
  --     let x' = genFreshName x
  --         k' = genFreshName "k"
  --      in EApp
  --           (Let x' value (ELam k' (cpsC (renameFreeOccurrences x x' e2) (reflect (EVar k')))))
  --           (reify k)
  -- =admin>  x' is fresh, so it is not free in reify k
  -- there, rename should push from the top EApp, into ELam, and then into the body of ELam
  --   cpsC e1 $ \value ->
  --     let x' = genFreshName x
  --         k' = genFreshName "k"
  --      in Let x' value
  --           (EApp (ELam k' (cpsC (renameFreeOccurrences x x' e2) (reflect (EVar k')))) (reify k))
  -- =beta>  apply the object-level continuation lambda to reify k
  --   cpsC e1 $ \value ->
  --     let x' = genFreshName x
  --         k' = genFreshName "k"
  --      in Let x' value
  --           (cpsC (renameFreeOccurrences x x' e2) (reflect (reify k)))
  -- =eta>
  cpsC e1 $ \value ->
    let x' = genFreshName x
     in Let x' value (cpsC (renameFreeOccurrences x x' e2) k)
cpsC (Letrec f x e1 e2) k =
  -- Letrec f x e1 e2 := Let f (EFix f x e1) e2
  -- where EFix binds the recursive name f in e1, like ELam binds x in e.
  -- Operationally, EFix f x e is the recursive knot satisfying
  --   EFix f x e = ELam x (e[f := EFix f x e])
  -- but the CPS conversion treats that knot as a value constructor, not as an
  -- application of an ordinary fix function.
  --
  -- The purpose of this branch is exactly to make that special recursive knot
  -- explicit. We first recognize that Fix is not just another lambda or
  -- application shape: it is the syntax that ties the recursive name back to
  -- the value being defined. Then we introduce EFix as the expression-level
  -- representation of that knot, so Letrec can be derived through Let + EFix
  -- instead of by pretending recursion is an ordinary function call.
  --
  -- Step labels:
  --   =meta>   expand cpsC / apply meta-level continuations
  --   =alpha>  object-language alpha-renaming
  --   =beta>   object-language beta reduction
  --   =admin>  administrative let rearrangement
  --   =eta>    reflect/reify eta reduction
  --
  -- First isolate the only new rule. EFix is value-like, so its CPS rule mirrors
  -- ELam, except that the generated continuation parameter is inserted inside
  -- the recursive knot:
  --
  -- cpsC (EFix f x e) k
  -- =meta>
  -- let k' = genFreshName "k"
  --  in k (EFix f x (ELam k' (cpsC e (reflect (EVar k')))))
  --
  -- This rule follows from what EFix denotes. EFix f x e is already the
  -- recursive function value: it ties f to the value being constructed, and
  -- that value accepts the ordinary argument x before running e. CPS conversion
  -- of a function value does not call the function immediately; it changes the
  -- value's shape so that, after x, it accepts a dynamic continuation k'. The
  -- body e is then converted under reflect (EVar k'), exactly as in the ELam
  -- rule. The outer continuation k receives the finished recursive value.
  --
  -- That is why the continuation parameter appears inside the EFix body as an
  -- extra lambda, while the recursive binding itself is still the same knot.
  -- We are tying f to the CPS-expanded value, not tying f to an ongoing call.
  --
  -- EFix therefore belongs with ELam, not with EApp. ELam and EFix both build
  -- values: ELam binds x in a function body, while EFix binds f and x in a
  -- recursive function body. EApp is different: it is a computation that first
  -- obtains a function, then obtains an argument, then performs a call with the
  -- current continuation. If EFix were treated like an EApp of an ordinary fix
  -- function, the conversion would force a call to fix during translation of
  -- the recursive value and would have to pass reify k to that call. That makes
  -- the recursive knot depend on the consumer continuation of the binding site,
  -- which is the wrong level: the knot should only describe the recursive value
  -- being bound, and each later call to that value supplies its own continuation.
  --
  -- This is the syntactic version of the observation above:
  --   Fix f = f (Fix f)
  --   FixF f k = f (Fix f) k
  --
  -- The important point is that Fix and FixF only tie the recursive binding.
  -- They do not know that k is a continuation, and they do not bind k as part
  -- of the recursive knot. Fix ties a name to a value of whatever function
  -- shape it has: in direct style the recursive value takes x; after CPS the
  -- same recursive value takes x and then k. The continuation is just the extra
  -- ordinary parameter introduced by CPS, so FixF is Fix at the CPS-expanded
  -- function shape, **not a continuation-aware fixed point operator**.
  --
  -- Now derive Letrec by expanding it through Let, but keeping EFix primitive.
  --
  -- cpsC (Let f (EFix f x e1) e2) k
  -- =meta>  expand Let as an object-level lambda application
  -- cpsC (EApp (ELam f e2) (EFix f x e1)) k
  -- =meta>
  -- cpsC (ELam f e2) $ \fun ->
  --   cpsC (EFix f x e1) $ \value ->
  --     EApp (EApp fun value) (reify k)
  -- =meta>
  -- cpsC (EFix f x e1) $ \value ->
  --   let k' = genFreshName "k"
  --    in EApp
  --         (EApp (ELam f (ELam k' (cpsC e2 (reflect (EVar k'))))) value)
  --         -- reify f = let a = genFreshName "a" in ELam a (f (EVar a))
  --         (reify k)
  -- =meta>
  -- let k'' = genFreshName "k"
  --  in let value = EFix f x (ELam k'' (cpsC e1 (reflect (EVar k''))))
  --      in let k' = genFreshName "k"
  --          in EApp
  --               (EApp (ELam f (ELam k' (cpsC e2 (reflect (EVar k'))))) value)
  --               (reify k)
  -- =meta>
  -- let k' = genFreshName "k"
  --     k'' = genFreshName "k"
  --  in EApp
  --       (EApp
  --         (ELam f (ELam k' (cpsC e2 (reflect (EVar k')))))
  --         (EFix f x (ELam k'' (cpsC e1 (reflect (EVar k''))))))
  --       (reify k)
  -- =alpha>  choosing f' fresh for e1, e2, and reify k
  -- let k' = genFreshName "k"
  --     k'' = genFreshName "k"
  --     f' = genFreshName f
  --  in EApp
  --       (EApp
  --         (ELam
  --           f'
  --           (ELam k' (cpsC (renameFreeOccurrences f f' e2) (reflect (EVar k')))))
  --         (EFix
  --           f'
  --           x
  --           (ELam k'' (cpsC (renameFreeOccurrences f f' e1) (reflect (EVar k''))))))
  --       (reify k)
  -- =beta>  turn the object-level lambda application into a let binding
  -- let k' = genFreshName "k"
  --     k'' = genFreshName "k"
  --     f' = genFreshName f
  --  in EApp
  --       (Let
  --         f'
  --         (EFix
  --           f'
  --           x
  --           (ELam k'' (cpsC (renameFreeOccurrences f f' e1) (reflect (EVar k'')))))
  --         (ELam k' (cpsC (renameFreeOccurrences f f' e2) (reflect (EVar k')))))
  --       (reify k)
  -- =admin>  fold Let f' (EFix f' x body) body2 back to Letrec
  -- let k' = genFreshName "k"
  --     k'' = genFreshName "k"
  --     f' = genFreshName f
  --  in EApp
  --       (Letrec
  --         f'
  --         x
  --         (ELam k'' (cpsC (renameFreeOccurrences f f' e1) (reflect (EVar k''))))
  --         (ELam k' (cpsC (renameFreeOccurrences f f' e2) (reflect (EVar k')))))
  --       (reify k)
  -- =admin>  f' is fresh, so it is not free in reify k
  -- let k' = genFreshName "k"
  --     k'' = genFreshName "k"
  --     f' = genFreshName f
  --  in Letrec
  --       f'
  --       x
  --       (ELam k'' (cpsC (renameFreeOccurrences f f' e1) (reflect (EVar k''))))
  --       (EApp
  --         (ELam k' (cpsC (renameFreeOccurrences f f' e2) (reflect (EVar k'))))
  --         (reify k))
  -- =beta>  apply the object-level continuation lambda to reify k
  -- let k'' = genFreshName "k"
  --     f' = genFreshName f
  --  in Letrec
  --       f'
  --       x
  --       (ELam k'' (cpsC (renameFreeOccurrences f f' e1) (reflect (EVar k''))))
  --       (cpsC (renameFreeOccurrences f f' e2) (reflect (reify k)))
  -- =eta>
  let
    k'' = genFreshName "k"
    f' = genFreshName f
   in
    Letrec
      f'
      x
      (ELam k'' (cpsC (renameFreeOccurrences f f' e1) (reflect (EVar k''))))
      (cpsC (renameFreeOccurrences f f' e2) k)
cpsC (EConstant n) k =
  k (EConstant n)
cpsC (EUnary op e) k =
  cpsC e $ \value ->
    k (EUnary op value)
cpsC (EBinary op e1 e2) k =
  cpsC e1 $ \value1 ->
    cpsC e2 $ \value2 ->
      k (EBinary op value1 value2)
cpsC (EFix f x e) k =
  -- EFix is a recursive value constructor, like ELam with an extra self binder.
  -- The outer k consumes the value; the fresh k' is the dynamic continuation
  -- accepted each time the recursive value is called.
  let k' = genFreshName "k"
   in k (EFix f x (ELam k' (cpsC e (reflect (EVar k')))))
