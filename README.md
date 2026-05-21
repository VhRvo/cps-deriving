# Thoughts

## Eta-redex strategies

The module `Good.FourEtaRedexStrategies` puts the four alternatives from the paper next to each other:

| Paper wording | Function |
| --- | --- |
| Leave the eta-redexes where they are | `cpsLeaveEta` / `topLevelLeaveEta` |
| Detect a newly constructed lambda that is an eta-redex | `cpsDetectEta` / `topLevelDetectEta` |
| Carry an inherited attribute identifying tail-call contexts | `cpsWithInheritedAttribute` / `topLevelInheritedTail` |
| Duplicate the rules for tail-call contexts | `cpsDuplicatedRules` and `cpsDuplicatedRulesTail` / `topLevelDuplicatedRules` |

For the inherited-attribute version, `TailContext` is the sum of the two continuation representations: `NonTail (Expr -> Expr)` for static continuations and `TailCall Var` for dynamic continuation variables. The shared `sampleTailCall` example is `\function -> function argument`. The test suite checks that the first strategy preserves the reified-continuation eta-redex `\a -> k a` in the CPS result, while the other three remove that redex without changing the direct tail-call shape.

## Formatting

To check if files are already formatted (useful on CI):

```bash
fourmolu --mode check .
```

Find all the source files in a project with `git ls-files` and then use `fourmulu` to format those files:

```bash
fourmolu --mode inplace $(git ls-files '*.hs')
# Or to avoid hitting command line length limits and enable parallelism (12-way here):
git ls-files -z '*.hs' | xargs -P 12 -0 fourmolu --mode inplace
```
