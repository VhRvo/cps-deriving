{-# LANGUAGE OverloadedStrings #-}

module Plain1.Conversion where

import Expr
import FreshName (genFreshName)

cps :: Expr -> Expr
cps (EVar n) =
  let k = genFreshName "k"
   in ELam k (EApp (EVar k) (EVar n))
cps (ELam n e) =
  let k = genFreshName "k"
   in ELam k (EApp (EVar k) (ELam n (cps e)))
cps (EApp e1 e2) =
  let
    k = genFreshName "k"
    fun = genFreshName "fun"
    arg = genFreshName "arg"
    e1' = cps e1
    e2' = cps e2
   in
    ELam
      k
      ( EApp
          e1'
          ( ELam
              fun
              ( EApp
                  e2'
                  ( ELam
                      arg
                      (EApp (EApp (EVar fun) (EVar arg)) (EVar k))
                  )
              )
          )
      )
