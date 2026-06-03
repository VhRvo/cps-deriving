# Thoughts

## Notes & references

- [Papers/Derivation-CCS-to-MCS.md](Papers/Derivation-CCS-to-MCS.md) — 从 CCS 到 MCS 的逻辑关系
  基本引理证明,以及 defunctionalize 出的 shift/reset 抽象机
  ([src/Shift/Machine/Eval.hs](src/Shift/Machine/Eval.hs))。
- [Papers/References.md](Papers/References.md) — 参考文献与理论谱系(Stoy / Reynolds / Plotkin /
  Danvy–Filinski / Bahr–Hutton),含"定理 ↔ 文献"速查表。

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
