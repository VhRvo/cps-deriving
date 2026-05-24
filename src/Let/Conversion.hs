{-# LANGUAGE OverloadedStrings #-}

module Let.Conversion where

import FreshName (genFreshName)
import Let.Expr
import Let.Rename (renameFreeOccurrences)

fix :: Expr
fix = EVar "fix"
-- bad
-- fix f = f (fix f)
--   [ fix ]
-- = [\f. f (fix f) ]
-- = \f_k k. [ f (fix f) ] k
-- = \f_k k. [f] $ \f_k -> [ fix f ] $ \app -> f_k app k
-- = \f_k k. [ fix f ] $ \app -> f_k app k
-- = \f_k k. [ fix ] $ \fix_k -> [ f ] $ \f_k -> fix_k f_k (\app -> f_k app k)
-- = \f_k k. [ f ] $ \f_k -> fix_k f_k (\app -> f_k app k)
-- = \f_k k. fix_k f_k (\app -> f_k app k)
-- good
-- fix f = f (\x . fix f x)
-- fix_k
-- = [ fix ] (\x. x)
-- = [ \f. f (\x. fix f x) ] (\x. x)
-- = (\x. x) (\f k. [ f (\x. fix f x) ] k)


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
  -- cpsC (EApp e1 e2) k =
  --   cpsC e1 $ \f ->
  --     cpsC e2 $ \arg ->
  --       EApp (EApp f arg) (reify k)

--   Letrec f x e1 e2 := Let f (EApp fix (ELam (ELam x e1))) e2

  --   cpsC (EApp fix (ELam f (ELam x e1))) $ \value ->
  --     let f' = genFreshName f
  --      in Let f' value (cpsC (renameFreeOccurrences f f' e2) k)

--   cpsC fix $ \fixF ->
--     cpsC (ELam f (ELam x e1)) $ \loop ->
--       EApp
--         (EApp fixF loop)
--         ( reify
--             ( \value ->
--                 let f' = genFreshName f
--                  in Let f' value (cpsC (renameFreeOccurrences f f' e2) k)
--             )
--         )

--   cpsC fix $ \fixF ->
--     let
--         -- loop = let k' = genFreshName "k" in ELam f (ELam k' (cpsC (ELam x e1) (reflect (EVar k'))))
--         -- loop = let k' = genFreshName "k" in ELam f (ELam k' (let k'' = genFreshName "k" in reflect (EVar k') (ELam x (ELam k'' (cpsC e1 (reflect (EVar k'')))))))
--         loop = let k' = genFreshName "k" in ELam f (ELam k' (let k'' = genFreshName "k" in EApp (EVar k') (ELam x (ELam k'' (cpsC e1 (reflect (EVar k'')))))))
--      in EApp
--           (EApp fixF loop)
--           ( reify
--               ( \value ->
--                   let f' = genFreshName f
--                       in Let f' value (cpsC (renameFreeOccurrences f f' e2) k)
--               )
--           )

  let
      loop = let k' = genFreshName "k" in ELam f (ELam k' (let k'' = genFreshName "k" in EApp (EVar k') (ELam x (ELam k'' (cpsC e1 (reflect (EVar k'')))))))
   in EApp
          (EApp fixF loop)
          ( reify
              ( \value ->
                  let f' = genFreshName f
                      in Let f' value (cpsC (renameFreeOccurrences f f' e2) k)
              )
          )

--   cpsC (EApp fix (ELam f (ELam x e1))) $ \value ->
--     let f' = genFreshName f
--      in Let f' value (cpsC (renameFreeOccurrences f f' e2) k)

--   undefined
--   let f' = genFreshName f
--     in Letrec f' e1 (cpsC (renameFreeOccurrences f f' e2) k)
cpsC (EConstant n) k =
  k (EConstant n)
cpsC (EUnary op e) k =
  cpsC e $ \value ->
    k (EUnary op value)
cpsC (EBinary op e1 e2) k =
  cpsC e1 $ \value1 ->
    cpsC e2 $ \value2 ->
      k (EBinary op value1 value2)
