{-# LANGUAGE OverloadedStrings #-}

module Good.FourEtaRedexStrategies
  ( Var,
    TailContext (..),
    containsEtaRedex,
    containsReifiedContinuationEtaRedex,
    cpsDetectEta,
    cpsDuplicatedRules,
    cpsDuplicatedRulesTail,
    cpsLeaveEta,
    cpsWithInheritedAttribute,
    cpsWithInheritedAttributeFromContext,
    sampleTailCall,
    topLevelDetectEta,
    topLevelDuplicatedRules,
    topLevelInheritedTail,
    topLevelLeaveEta,
  )
where

import Data.Text (Text)
import Expr
import FreshName (genFreshName)

data TailContext
  = NonTail (Expr -> Expr)
  | TailCall Var

reflect :: Var -> Expr -> Expr
reflect continuationName = EApp (EVar continuationName)

reifyKeepingEta :: (Expr -> Expr) -> Expr
reifyKeepingEta staticCont =
  let resultName = genFreshName "a"
   in ELam resultName (staticCont (EVar resultName))

reifyDetectingEta :: (Expr -> Expr) -> Expr
reifyDetectingEta staticCont =
  let resultName = genFreshName "a"
   in contractEtaAtConstruction resultName (staticCont (EVar resultName))

contractEtaAtConstruction :: Var -> Expr -> Expr
contractEtaAtConstruction parameterName bodyExpr =
  case bodyExpr of
    EApp functionExpr (EVar argumentName)
      | argumentName == parameterName && not (occursFree parameterName functionExpr) ->
          functionExpr
    _ -> ELam parameterName bodyExpr

occursFree :: Var -> Expr -> Bool
occursFree variableName (EVar currentName) = variableName == currentName
occursFree variableName (ELam parameterName bodyExpr) =
  variableName /= parameterName && occursFree variableName bodyExpr
occursFree variableName (EApp functionExpr argumentExpr) =
  occursFree variableName functionExpr || occursFree variableName argumentExpr

containsEtaRedex :: Expr -> Bool
containsEtaRedex (ELam parameterName (EApp functionExpr (EVar argumentName)))
  | parameterName == argumentName && not (occursFree parameterName functionExpr) = True
containsEtaRedex (EVar _) = False
containsEtaRedex (ELam _ bodyExpr) = containsEtaRedex bodyExpr
containsEtaRedex (EApp functionExpr argumentExpr) =
  containsEtaRedex functionExpr || containsEtaRedex argumentExpr

containsReifiedContinuationEtaRedex :: Expr -> Bool
containsReifiedContinuationEtaRedex (ELam parameterName (EApp (EVar _) (EVar argumentName)))
  | parameterName == argumentName = True
containsReifiedContinuationEtaRedex (EVar _) = False
containsReifiedContinuationEtaRedex (ELam _ bodyExpr) = containsReifiedContinuationEtaRedex bodyExpr
containsReifiedContinuationEtaRedex (EApp functionExpr argumentExpr) =
  containsReifiedContinuationEtaRedex functionExpr || containsReifiedContinuationEtaRedex argumentExpr

-- 1. Leave eta-redexes alone: every dynamic continuation is reified as \a -> k a.
cpsLeaveEta :: Expr -> (Expr -> Expr) -> Expr
cpsLeaveEta (EVar variableName) staticCont =
  staticCont (EVar variableName)
cpsLeaveEta (ELam parameterName bodyExpr) staticCont =
  let continuationName = genFreshName "k"
   in staticCont
        (ELam parameterName (ELam continuationName (cpsLeaveEta bodyExpr (reflect continuationName))))
cpsLeaveEta (EApp functionExpr argumentExpr) staticCont =
  cpsLeaveEta functionExpr $ \functionValue ->
    cpsLeaveEta argumentExpr $ \argumentValue ->
      EApp (EApp functionValue argumentValue) (reifyKeepingEta staticCont)

-- 2. Detect eta-redexes exactly when the fresh lambda is constructed.
cpsDetectEta :: Expr -> (Expr -> Expr) -> Expr
cpsDetectEta (EVar variableName) staticCont =
  staticCont (EVar variableName)
cpsDetectEta (ELam parameterName bodyExpr) staticCont =
  let continuationName = genFreshName "k"
   in staticCont
        (ELam parameterName (ELam continuationName (cpsDetectEta bodyExpr (reflect continuationName))))
cpsDetectEta (EApp functionExpr argumentExpr) staticCont =
  cpsDetectEta functionExpr $ \functionValue ->
    cpsDetectEta argumentExpr $ \argumentValue ->
      EApp (EApp functionValue argumentValue) (reifyDetectingEta staticCont)

-- 3. Carry an inherited attribute saying whether this expression is a tail call.
cpsWithInheritedAttribute :: Expr -> Var -> Expr
cpsWithInheritedAttribute inputExpr continuationName =
  cpsWithInheritedAttributeFromContext (TailCall continuationName) inputExpr

cpsWithInheritedAttributeFromContext :: TailContext -> Expr -> Expr
cpsWithInheritedAttributeFromContext tailContext (EVar variableName) =
  applyContext tailContext (EVar variableName)
cpsWithInheritedAttributeFromContext tailContext (ELam parameterName bodyExpr) =
  let continuationName = genFreshName "k"
   in applyContext
        tailContext
        ( ELam
            parameterName
            (ELam continuationName (cpsWithInheritedAttributeFromContext (TailCall continuationName) bodyExpr))
        )
cpsWithInheritedAttributeFromContext tailContext (EApp functionExpr argumentExpr) =
  cpsWithInheritedAttributeFromContext
    ( NonTail $ \functionValue ->
        cpsWithInheritedAttributeFromContext
          ( NonTail $ \argumentValue ->
              EApp (EApp functionValue argumentValue) (continuationTerm tailContext)
          )
          argumentExpr
    )
    functionExpr

applyContext :: TailContext -> Expr -> Expr
applyContext (NonTail staticCont) valueExpr = staticCont valueExpr
applyContext (TailCall continuationName) valueExpr = reflect continuationName valueExpr

continuationTerm :: TailContext -> Expr
continuationTerm (TailCall continuationName) = EVar continuationName
continuationTerm (NonTail staticCont) = reifyKeepingEta staticCont

-- 4. Duplicate the rules: one function for ordinary contexts, one for tail contexts.
cpsDuplicatedRules :: Expr -> (Expr -> Expr) -> Expr
cpsDuplicatedRules (EVar variableName) staticCont =
  staticCont (EVar variableName)
cpsDuplicatedRules (ELam parameterName bodyExpr) staticCont =
  let continuationName = genFreshName "k"
   in staticCont
        (ELam parameterName (ELam continuationName (cpsDuplicatedRulesTail bodyExpr continuationName)))
cpsDuplicatedRules (EApp functionExpr argumentExpr) staticCont =
  cpsDuplicatedRules functionExpr $ \functionValue ->
    cpsDuplicatedRules argumentExpr $ \argumentValue ->
      EApp (EApp functionValue argumentValue) (reifyKeepingEta staticCont)

cpsDuplicatedRulesTail :: Expr -> Var -> Expr
cpsDuplicatedRulesTail (EVar variableName) continuationName =
  EApp (EVar continuationName) (EVar variableName)
cpsDuplicatedRulesTail (ELam parameterName bodyExpr) continuationName =
  let bodyContinuationName = genFreshName "k"
   in EApp
        (EVar continuationName)
        ( ELam
            parameterName
            (ELam bodyContinuationName (cpsDuplicatedRulesTail bodyExpr bodyContinuationName))
        )
cpsDuplicatedRulesTail (EApp functionExpr argumentExpr) continuationName =
  cpsDuplicatedRules functionExpr $ \functionValue ->
    cpsDuplicatedRules argumentExpr $ \argumentValue ->
      EApp (EApp functionValue argumentValue) (EVar continuationName)

sampleTailCall :: Expr
sampleTailCall = ELam "function" (EApp (EVar "function") (EVar "argument"))

topLevelLeaveEta :: Expr -> Var -> Expr
topLevelLeaveEta inputExpr continuationName = cpsLeaveEta inputExpr (reflect continuationName)

topLevelDetectEta :: Expr -> Var -> Expr
topLevelDetectEta inputExpr continuationName = cpsDetectEta inputExpr (reflect continuationName)

topLevelInheritedTail :: Expr -> Var -> Expr
topLevelInheritedTail = cpsWithInheritedAttribute

topLevelDuplicatedRules :: Expr -> Var -> Expr
topLevelDuplicatedRules = cpsDuplicatedRulesTail
