# Deriving Meta-Continuation Semantics from `evalK`

Given the definition of `evalK`:

```haskell
evalK env (Var x) k =
  k (env x)

evalK env (Lam x body) k =
  k (\v k' -> evalK (env[x |-> v]) body k')

evalK env (App e1 e2) k =
  evalK env e1 (\f -> evalK env e2 (\a -> f a k))

evalK env (Reset body) k =
  k (evalK env body (\x -> x))

evalK env (Shift c body) k =
  evalK (env[c |-> \v k' -> k' (k v)]) body (\x -> x)

evalK env (CallCC c body) k =
  evalK (env[c |-> \v k' -> k v]) body k
```

The authors said:

> We can treat a semantics written in continuation-composing style as a direct semantics and obtain a strategy-independent "meta-continuation semantics" from it by the standard CPS conversion.

The idea is to treat `evalK` *as if* it were a direct-style semantic function and
apply one more CPS conversion to it. The extra continuation introduced by this CPS
conversion is the meta-continuation.

### Why are we allowed to treat `evalK` as direct?

`evalK` is manifestly *not* direct-style: it already takes a continuation `k`.
The word that makes the trick legal is **continuation-composing**.

In continuation-composing style the answer type equals the value type:

```haskell
evalK env expr k  ::  Value          -- answer type Ans_c = Value
k                 ::  Value -> Value -- so Cont_c = Value -> Value
```

Because the answer type is `Value`, the expression `evalK env expr k` has exactly
the *shape* of a direct semantics `eval env expr :: Value` that simply returns a
value. That shape is all the standard CPS conversion needs. We are not pretending
`k` does not exist; we are exploiting the fact that the whole CCS computation
*produces a value*, and CPS-converting a value-producing computation is routine.

Contrast this with a genuinely effectful direct semantics whose answer type is
some `Ans /= Value`: there `Cont = Value -> Ans` cannot be composed as
`k' (k v)`, and the second CPS pass would not line up. The equality
`Ans_c = Value` is the root reason the whole construction works.

### Where the "composing" actually happens

It pays to locate, up front, the *only* two places where `evalK` composes
continuations rather than merely tail-calling them:

```haskell
-- Reset: the inner computation's answer becomes an argument to k
k (evalK env body (\x -> x))

-- Shift: the captured continuation k is composed under the current k'
\v k' -> k' (k v)
```

Everything else in `evalK` is a tail call. These two composition sites are:

* the literal origin of the name *continuation-composing*;
* the only subterms that are *nontrivial* (nested) for the second CPS pass, hence
  the only places that require the unprimed (static-continuation) translation;
* the only places where the meta-continuation structure is actually generated.

Keeping this map in mind, the rest of the derivation is bookkeeping.

## What is Being CPS-Transformed?

There are three levels that should not be conflated.

First, there is the original object-language:

```haskell
Var x
Lam x body
App e1 e2
Reset body
Shift c body
CallCC c body
```

The parameter `expr` is an expression of this object-language.

Second, there is the original meta-language evaluator:

```haskell
evalK env expr k
```

At this level, `evalK` is not an object-language term. It is a meta-language function defining the semantics of the object-language.

Third, when deriving `evalMK`, we temporarily treat the right-hand sides of the `evalK` equations as source expressions for another CPS transformation.

So `evalK` does not become the original object-language. Rather, the meta-language expressions defining `evalK` become the object being transformed by CPS conversion.

CPS conversion is a syntactic transformation.

It does not run `evalK`. It rewrites the syntax of the meta-language expressions that appear in the right-hand sides of the `evalK` equations. This is why we must say explicitly which meta-language phrases are treated as source syntax for the transformation and which phrases are treated as atomic primitives.

For example:

```haskell
env x
```

is syntactically an application in the meta-language, but semantically it is just a pure environment lookup. Since it has no control effect, we classify it as an atomic source phrase for this CPS transformation.

By contrast:

```haskell
k v
f a k
evalK env e k
```

are control-relevant source phrases for this transformation, so they are translated into the meta-CPS world.

For this reason, the specification:

```haskell
evalMK env expr k mk = [[ evalK env expr k ]]' mk
```

should be read as shorthand for:

```haskell
evalMK env expr k mk =
  CPS'[[ the meta-language expression defining `evalK env expr k` ]] mk
```

or, case by case:

```haskell
evalMK env (Var x) k mk =
  [[ k (env x) ]]' mk

evalMK env (Lam x body) k mk =
  [[ k (\v k' -> evalK (env[x |-> v]) body k') ]]' mk

evalMK env (App e1 e2) k mk =
  [[ evalK env e1 (\f -> evalK env e2 (\a -> f a k)) ]]' mk
```

and similarly for the other clauses.

To avoid administrative redexes and eta-redexes in the derivation, it is better to follow the notation from Danvy and Filinski's *Representing Control*:

```haskell
[[ M ]]  kappa
[[ M ]]' mk
```

The two translations mean different things.

`[[ M ]] kappa` is the one-pass CPS translation with a static continuation `kappa`. Here `kappa` is a meta-level function that receives the result of `M` and builds the rest of the translated term.

`[[ M ]]' mk` is the properly tail-recursive auxiliary translation. It is used when the continuation is already a named dynamic continuation `mk`. It avoids constructing the eta-redex:

```haskell
\x -> mk x
```

The intended relationship is beta/eta equivalence:

```haskell
[[ M ]]' mk  =beta-eta=  [[ M ]] (\x -> mk x)
```

but `[[ M ]]'` is defined directly, so the eta-redex is never generated.

With the caveat above, we will continue to use the shorthand:

```haskell
evalMK env expr k mk = [[ evalK env expr k ]]' mk
```

Here:

```haskell
k  :: value -> meta-continuation -> answer
mk :: value -> answer
```

That is, after the extra CPS conversion, ordinary continuations receive one more argument: the meta-continuation.

### Reading the shorthand: a substitution convention

The shorthand reuses the name `k` at two different types, and this must be made
explicit. On the left, the `k` parameter of `evalMK` is the *transformed*
continuation

```haskell
k :: value -> meta-continuation -> answer
```

while inside `[[ evalK env expr k ]]'` the `k` is the *original* CCS continuation

```haskell
k :: value -> value
```

The equation is therefore schematic: it is understood that **every free value
and continuation variable on the right is silently replaced by its own
transform**. This is exactly why, later, we may write `[[ k ]]_v = k`: the
variable's transform is again the variable, only at the new type. Whenever a
clause reuses a name like `k`, `f`, `a`, read it as "the transformed thing that
this name now stands for."

### What "correct" means here

The equation above is a **syntactic** specification: it says what code the
translator emits. It is *not yet* a statement of semantic correctness. The
intended semantic criterion is the congruence

```haskell
evalMK env e k_mc mk  =  mk (evalK env e k_c)      -- with k_mc related to k_c
```

and a subtlety hides in it: at **procedure type** the two sides are *not* equal
as raw values, because a transformed closure carries an extra `mk'` argument that
the original closure does not. So `mk (evalK env e k_c)` cannot be taken
literally for results that are procedures. Establishing correctness requires a
**logical relation** that relates `k_mc` to `k_c` and relates transformed
procedures to original ones (the meta-continuation must "respect" the value
relation at the identity-continuation boundary). The syntactic derivation below
produces the *formulas*; the logical-relation argument (see
`Papers/Derivation-CCS-to-MCS.md`) is what proves them correct.

## Trivial and Nontrivial Expressions

The environment lookup:

```haskell
env x
```

is treated as a trivial meta-level operation.

It is not an object-language function call. It is a pure environment lookup in the meta-language, and it has no control effect. It does not capture, call, abort, or compose continuations.

So we treat it as atomic:

```haskell
[[ env x ]]_v = env x
```

This is not an isolated exception. It is an instance of a larger class of trivial meta-level operations.

Atomic or trivial meta-level expressions include:

```haskell
x
v
f
a
k
k'
env
body
e1
e2
```

meta-language variables;

```haskell
env x
```

pure environment lookup;

```haskell
env[x |-> value]
env[c |-> value]
```

pure environment extension, assuming `value` has already been translated if necessary;

```haskell
Var x
Lam x body
App e1 e2
Reset body
Shift c body
CallCC c body
```

object-language syntax constructors, when they occur merely as data.

For example:

```haskell
env[c |-> \v k' -> k' (k v)]
```

should not be CPS-transformed by treating `env[...]` itself as a control-relevant application. The environment-extension operation is atomic. However, the value being inserted into the environment is a function value, so that value must still be translated:

```haskell
[[ \v k' -> k' (k v) ]]_v =
  \v k' mk' -> k v (\x -> k' x mk')
```

So the translated environment extension becomes:

```haskell
env[c |-> \v k' mk' -> k v (\x -> k' x mk')]
```

In contrast, the following expressions are nontrivial computations and must be translated into the meta-CPS world:

```haskell
k v
```

continuation application;

```haskell
f a k
```

application of an object-language function value to an argument and a continuation;

```haskell
evalK env e k
```

recursive semantic evaluation.

So it is not accurate to say that the CPS application rule is needed only when the function position is a continuation. The standard CPS application rule applies to applications in general. However, after treating `env x` as atomic and recognizing recursive calls to `evalK`, the continuation applications such as `k ...` and `k' ...` are the places where the meta-continuation structure is most visible.

## Useful Translation Schemas

The value translation:

```haskell
[[ V ]]_v
```

is also a syntactic translation. It is defined only for value syntax `V`, not for arbitrary computations.

It is related to the unprimed computation translation by the value clause:

```haskell
[[ V ]] kappa =
  kappa ([[ V ]]_v)
```

Therefore, for value syntax `V` only:

```haskell
[[ V ]]_v = [[ V ]] id_static
```

where:

```haskell
id_static = \x -> x
```

is the static identity continuation used by the translator.

This equation should not be read as a rule for arbitrary expressions:

```haskell
[[ M ]]_v = [[ M ]] id_static
```

because `[[ M ]]_v` is not defined when `M` is a non-value computation such as `k v`, `f a k`, or `evalK env e k`.

When an unprimed translation has a static continuation:

```haskell
[[ M ]] kappa
```

the `kappa` is not a runtime continuation value. It is a meta-level function used by the translator.

Therefore, when `kappa` must be passed to an already transformed function or continuation, it must first be reified as a dynamic meta-continuation:

```haskell
reify kappa =
  \x -> kappa x
```

This reification step is exactly where eta-redexes can be introduced. The primed translation `[[ M ]]' mk` avoids this when the continuation is already a named dynamic meta-continuation `mk`.

For atomic values:

```haskell
[[ A ]] kappa =
  kappa A

[[ A ]]' mk =
  mk A
```

For a continuation application whose argument is already atomic:

```haskell
[[ k A ]] kappa =
  k A (reify kappa)

[[ k A ]]' mk =
  k A mk
```

For a continuation application whose argument is nontrivial:

```haskell
[[ k M ]] kappa =
  [[ M ]] (\v -> k v (reify kappa))

[[ k M ]]' mk =
  [[ M ]] (\v -> k v mk)
```

The argument `M` must be evaluated first, and its result is then passed to `k`.

For an object-language function application, when `f`, `a`, and `k` are already values:

```haskell
[[ f a k ]] kappa =
  f a k (reify kappa)

[[ f a k ]]' mk =
  f a k mk
```

For recursive semantic evaluation:

```haskell
[[ evalK env e k ]] kappa =
  evalMK env e [[ k ]]_v (reify kappa)

[[ evalK env e k ]]' mk =
  evalMK env e [[ k ]]_v mk
```

For lambda values:

```haskell
[[ \x -> M ]]_v =
  \x mk -> [[ M ]]' mk

[[ \v k' -> M ]]_v =
  \v k' mk -> [[ M ]]' mk
```

The identity continuation is therefore translated as:

```haskell
[[ \x -> x ]]_v =
  \x mk -> mk x
```

## Var

```haskell
evalMK env (Var x) k mk
= [[ evalK env (Var x) k ]]' mk
= [[ k (env x) ]]' mk
= k (env x) mk
```

Therefore:

```haskell
evalMK env (Var x) k mk =
  k (env x) mk
```

Here `env x` is atomic, while `k (env x)` is a continuation application.

## Lam

```haskell
evalMK env (Lam x body) k mk
= [[ evalK env (Lam x body) k ]]' mk
= [[ k (\v k' -> evalK (env[x |-> v]) body k') ]]' mk
= k [[ \v k' -> evalK (env[x |-> v]) body k' ]]_v mk
= k
    (\v k' mk' -> [[ evalK (env[x |-> v]) body k' ]]' mk')
    mk
= k
    (\v k' mk' -> evalMK (env[x |-> v]) body k' mk')
    mk
```

Therefore:

```haskell
evalMK env (Lam x body) k mk =
  k
    (\v k' mk' -> evalMK (env[x |-> v]) body k' mk')
    mk
```

The closure receives an extra meta-continuation argument `mk'`.

## App

```haskell
evalMK env (App e1 e2) k mk
= [[ evalK env (App e1 e2) k ]]' mk
= [[ evalK env e1 (\f -> evalK env e2 (\a -> f a k)) ]]' mk
= evalMK env e1
    [[ \f -> evalK env e2 (\a -> f a k) ]]_v
    mk
= evalMK env e1
    (\f mk' -> [[ evalK env e2 (\a -> f a k) ]]' mk')
    mk
= evalMK env e1
    (\f mk' ->
      evalMK env e2
        [[ \a -> f a k ]]_v
        mk')
    mk
= evalMK env e1
    (\f mk' ->
      evalMK env e2
        (\a mk'' -> [[ f a k ]]' mk'')
        mk')
    mk
= evalMK env e1
    (\f mk' ->
      evalMK env e2
        (\a mk'' -> f a k mk'')
        mk')
    mk
```

Therefore:

```haskell
evalMK env (App e1 e2) k mk =
  evalMK env e1
    (\f mk' ->
      evalMK env e2
        (\a mk'' -> f a k mk'')
        mk')
    mk
```

The expression:

```haskell
f a k
```

also uses application conversion. Since `f`, `a`, and `k` are already values in this context, it simplifies directly to:

```haskell
[[ f a k ]]' mk'' = f a k mk''
```

## Reset

```haskell
evalMK env (Reset body) k mk
= [[ evalK env (Reset body) k ]]' mk
= [[ k (evalK env body (\x -> x)) ]]' mk
= [[ evalK env body (\x -> x) ]] (\v -> k v mk)
= evalMK env body
    [[ \x -> x ]]_v
    (reify (\v -> k v mk))
= evalMK env body
    [[ \x -> x ]]_v
    (\v -> k v mk)
= evalMK env body
    (\x mk' -> mk' x)
    (\v -> k v mk)
```

Therefore:

```haskell
evalMK env (Reset body) k mk =
  evalMK env body
    (\x mk' -> mk' x)
    (\v -> k v mk)
```

The important point is that:

```haskell
k (evalK env body (\x -> x))
```

is a continuation application whose argument is nontrivial. Therefore the body is evaluated first, under the identity continuation, and its result is passed to `k`.

Notice that this case uses the unprimed translation:

```haskell
[[ evalK env body (\x -> x) ]] (\v -> k v mk)
```

because the continuation for the body is not just a named dynamic continuation. It is the static composition:

```haskell
\v -> k v mk
```

Before passing it to `evalMK`, this static continuation is reified:

```haskell
reify (\v -> k v mk)
= \x -> (\v -> k v mk) x
= \x -> k x mk
```

Note that here `reify` is, modulo alpha-renaming, a no-op: the static
continuation `\v -> k v mk` is already a genuine composition whose body
`k v mk` is *not* of the form `k v`, so reifying it cannot produce an
eta-redex `\x -> mk x`. Reification only matters when the static continuation
would otherwise be a bare meta-continuation name; that is the case the primed
translation is designed to avoid. Here `\x -> k x mk` and `\v -> k v mk` are
the same continuation, and we keep the latter in the final equation.

This is an essential composition, not an eta-redex.

## Shift

```haskell
evalMK env (Shift c body) k mk
= [[ evalK env (Shift c body) k ]]' mk
= [[ evalK (env[c |-> \v k' -> k' (k v)]) body (\x -> x) ]]' mk
= evalMK
    (env[c |-> [[ \v k' -> k' (k v) ]]_v])
    body
    [[ \x -> x ]]_v
    mk
```

Now translate the captured continuation:

```haskell
[[ \v k' -> k' (k v) ]]_v
= \v k' mk' -> [[ k' (k v) ]]' mk'
= \v k' mk' -> [[ k v ]] (\x -> k' x mk')
= \v k' mk' -> k v (reify (\x -> k' x mk'))
= \v k' mk' -> k v (\x -> k' x mk')
```

and:

```haskell
[[ \x -> x ]]_v =
  \x mk'' -> mk'' x
```

Therefore:

```haskell
evalMK env (Shift c body) k mk =
  evalMK
    (env[c |-> \v k' mk' -> k v (\x -> k' x mk')])
    body
    (\x mk'' -> mk'' x)
    mk
```

The body:

```haskell
k' (k v)
```

contains nested continuation applications. The inner application `k v` is evaluated first, and its result is passed to `k'`:

```haskell
\v k' mk' -> k v (\x -> k' x mk')
```

This is why the captured continuation for `Shift` is composable.

## CallCC

```haskell
evalMK env (CallCC c body) k mk
= [[ evalK env (CallCC c body) k ]]' mk
= [[ evalK (env[c |-> \v k' -> k v]) body k ]]' mk
= evalMK
    (env[c |-> [[ \v k' -> k v ]]_v])
    body
    [[ k ]]_v
    mk
```

Here `k` is already a transformed continuation value, so:

```haskell
[[ k ]]_v = k
```

Now translate the captured continuation:

```haskell
[[ \v k' -> k v ]]_v
= \v k' mk' -> [[ k v ]]' mk'
= \v k' mk' -> k v mk'
```

Therefore:

```haskell
evalMK env (CallCC c body) k mk =
  evalMK
    (env[c |-> \v k' mk' -> k v mk'])
    body
    k
    mk
```

The current continuation `k'` is ignored. Therefore the captured continuation is abortive:

```haskell
\v k' mk' -> k v mk'
```

## Final Meta-Continuation Semantics

Putting everything together:

```haskell
evalMK env (Var x) k mk =
  k (env x) mk

evalMK env (Lam x body) k mk =
  k
    (\v k' mk' -> evalMK (env[x |-> v]) body k' mk')
    mk

evalMK env (App e1 e2) k mk =
  evalMK env e1
    (\f mk' -> evalMK env e2
      (\a mk'' -> f a k mk'')
      mk')
    mk

evalMK env (Reset body) k mk =
  evalMK env body
    (\x mk' -> mk' x)
    (\v -> k v mk)

evalMK env (Shift c body) k mk =
  evalMK
    (env[c |-> \v k' mk' -> k v (\x -> k' x mk')])
    body
    (\x mk'' -> mk'' x)
    mk

evalMK env (CallCC c body) k mk =
  evalMK
    (env[c |-> \v k' mk' -> k v mk'])
    body
    k
    mk
```

The key difference between `Shift` and `CallCC` is:

```haskell
-- Shift: composable continuation
\v k' mk' -> k v (\x -> k' x mk')
```

versus:

```haskell
-- CallCC: abortive continuation
\v k' mk' -> k v mk'
```

`Shift` composes the captured continuation `k` with the current continuation `k'`.

`CallCC` ignores the current continuation `k'` and jumps directly to the captured continuation `k`.
