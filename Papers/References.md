# 参考文献与理论谱系

本文件整理 `Papers/` 中论文所依赖的理论谱系,重点是"把 continuation-composing style (CCS)
语义当作 direct semantics、用**逻辑关系 (logical relation)** 证明它与 standard CPS conversion
得到的 meta-continuation 语义 (MCS) 一致"这一方法论的源头。每条文献都标注了它在本仓库讨论中
对应的**具体定理/技术**。

> 注:下列 DOI/ISBN/URL 凭记忆给出,**正式引用前请逐条核对**(尤其 PRG technical monograph
> 编号与早期论文 DOI)。Stoy 1977 (MIT Press) 这本是确定的。

---

## 0. 仓库内的一手论文(`Papers/`)

- **Olivier Danvy & Andrzej Filinski. _Abstracting Control_. LFP 1990.**
  (`Papers/Abstracting Control.pdf`) — DOI: `10.1145/91556.91622`(待核对)
  - 第 1 节:从 CCS 的 shift/reset 语义,经 "standard CPS conversion" 得到 strategy-independent
    的 meta-continuation semantics。本仓库 `src/Shift/` 一系讨论的主线。
  - 关键事实:CCS 的答案类型 `Ans_c = Val`,故 `Cont_c = Val -> Val`,continuation 可复合
    (`κ'(κ v)`)。MCS 用 meta-continuation `γ : Val -> Ans` 把值-答案搬到真答案。

- **Olivier Danvy & Andrzej Filinski. _Representing Control: a Study of the CPS Transformation_.
  Mathematical Structures in Computer Science 2(4):361–391, 1992.**
  (`Papers/Representing Control- a Study of the CPS Transformation （Preprint）.pdf`)
  — DOI: `10.1017/S0960129500001535`(待核对)
  - one-pass CPS、administrative redex 的消除、static/dynamic continuation 的区分。
  - 对应本仓库 `Good/`、`OnePassTailRecursive/` 的 η-redex 消除讨论。

- **Patrick Bahr & Graham Hutton. _Calculating Correct Compilers_. Journal of Functional
  Programming 25, 2015.**
  (`Papers/Calculating Correct Compilers.pdf`) — DOI: `10.1017/S0956796815000180`(待核对)
  - 从正确性规范出发**构造性归纳**地计算编译器(specification-driven calculation)。
  - §5 rule induction:处理非组合 (non-compositional) 大步语义。
  - CPS + defunctionalization (Reynolds 1972) 推出抽象机。
  - 对应本对话:把 MCS 方程的推导改写成 Bahr–Hutton 风格 calculation;以及
    "stepwise(机械 CPS,正确性=一次性元定理)vs combined(规范驱动,正确性逐 case 重证)"
    的区分。

---

## 1. 核心奠基:Scott–Strachey 纲领与 Stoy

- **Joseph E. Stoy. _Denotational Semantics: The Scott–Strachey Approach to Programming
  Language Theory_. MIT Press, 1977.** ★ 必看 — ISBN: `0-262-19147-4` / `978-0-262-19147-0`
  - Scott 域 / 格论 / 连续函数 / 最小不动点:语义的数学地基。
  - λ-演算与语义元语言:`𝓔[[·]]ρκ` 这套 notation 的来源。
  - continuation(续延)语义:direct vs continuation 的写法与动机。
  - **"Relating different semantics" / congruence 证明**:本对话用逻辑关系把 CCS 与 MCS
    钉成相等的**方法源头**。
  - **inclusive (admissible) predicates 与 computation induction**:
    - "Comp-rel" 中 **Comp = Computation**(Stoy 的术语),非 Composition。
    - 加 `fix`/`Y` 时所需的"域论 admissibility"(谓词对 ω-链上确界封闭 + 含 ⊥),
      用于 Scott 不动点归纳。

- **Christopher Strachey & Christopher P. Wadsworth. _Continuations: A Mathematical Semantics
  for Handling Full Jumps_. Oxford PRG Technical Monograph PRG-11, 1974.**
  (后重刊于 _Higher-Order and Symbolic Computation_ 13(1/2):135–152, 2000)
  — 重刊 DOI: `10.1023/A:1010026413531`(待核对)
  - 续延语义的奠基文献;Stoy 书中续延一章的直接来源。

- **Dana Scott & Christopher Strachey. _Toward a Mathematical Semantics for Computer
  Languages_. Oxford PRG-6, 1971.**
  - Scott–Strachey 纲领的起点。

---

## 2. 逻辑关系 / CPS 正确性 / Defunctionalization

- **John C. Reynolds. _Definitional Interpreters for Higher-Order Programming Languages_.
  ACM '72;重刊于 _Higher-Order and Symbolic Computation_ 11(4):363–397, 1998.**
  — 重刊 DOI: `10.1023/A:1010027404223`(待核对)
  - **defunctionalization** + 逻辑关系的源头。
  - 对应本对话第 3 部分:对 MCS 的两层函数空间 (`Cont`, `MCont`) 做 defunctionalization,
    得到带 meta-continuation 栈的抽象机(见 `src/Shift/Machine/Eval.hs`)。
    这就是 Reynolds 的 "functional correspondence" 在分隔控制上的实例。

- **John C. Reynolds. _On the Relation between Direct and Continuation Semantics_.
  ICALP 1974, Springer LNCS 14, pp. 141–156.** — DOI: `10.1007/3-540-06841-4_65`(待核对)
  - **直接语义 vs 续延语义一致性**——与本对话所做的事最贴近的经典。

- **Gordon D. Plotkin. _Call-by-name, Call-by-value and the λ-calculus_.
  Theoretical Computer Science 1(2):125–159, 1975.** — DOI: `10.1016/0304-3975(75)90017-1`(待核对)
  - CPS 翻译的 **simulation / indifference** 定理 —— 本对话"基本引理 (Fundamental Lemma)"
    的祖宗。
  - "答案类型可观测"这条假设(本对话中 admissibility / 尊重性自动成立的根据)即出自此传统。

- **Gordon D. Plotkin. _LCF Considered as a Programming Language_.
  Theoretical Computer Science 5(3):223–255, 1977.** — DOI: `10.1016/0304-3975(77)90044-5`(待核对)
  - computational adequacy 与 **admissible predicates** 的标准处理。
  - 对应"第二种 admissibility":加 `fix` 后,验证整个逻辑关系 inclusive、可过 Scott 归纳。

---

## 3. 抽象机 / functional correspondence(延伸)

- **Mads Sjøberg Ager, Dariusz Biernacki, Olivier Danvy, Jan Midtgaard.
  _A Functional Correspondence between Evaluators and Abstract Machines_. PPDP 2003.**
  — DOI: `10.1145/888251.888254`(待核对;作者名拼写请核对)
  - CPS + defunctionalization ⟷ 抽象机的系统化对应。

- **Dariusz Biernacka, Olivier Danvy 等. _An Operational Foundation for Delimited Continuations_.**
  - shift/reset 的 CK + meta-stack 抽象机 —— 即 `src/Shift/Machine/Eval.hs` 里
    `K`(控制栈)+ `C`(元控制栈)两层栈的操作语义对应物。

---

## 4. 本对话用到的定理 ↔ 文献 速查

| 本对话中的对象 | 出处/传统 |
|---|---|
| 逻辑关系 ∼_V / ∼_K / ∼_P / ∼_C | Reynolds, Plotkin, Stoy |
| 基本引理 (Fundamental Lemma) = congruence `𝓔_mc ρ κ γ = γ(𝓔_c ρ κ)` | Plotkin 1975 simulation;Stoy 1977 relating semantics |
| R-Proc(应用 case 唯一被迫使用) | 逻辑关系在 Proc 类型的实例 |
| if-distrib(= γ 与 meta-`if` 交换) | "已求值布尔的条件是 administrative redex" (Plotkin CPS) |
| admissibility / "γ 尊重 ∼_V" | "答案类型可观测" 假设 (Reynolds/Plotkin);名字易与 Stoy 的域论 admissibility 混淆 |
| 域论 admissibility(inclusive predicate, Scott 归纳) | Stoy 1977;Plotkin 1977 (LCF) |
| Comp = Computation | Stoy 1977 术语 |
| stepwise vs combined 推导 | Bahr–Hutton 2015 §2.5/§2.6 |
| CPS + defunctionalization → 抽象机 | Reynolds 1972;Ager et al. 2003 |

---

## 5. 建议阅读顺序

1. **Stoy 1977**,〈relating semantics〉与〈inclusive predicates〉两章。
2. **Reynolds 1974**(direct vs continuation semantics)。
3. **Plotkin 1975**(CPS simulation / indifference)。
4. **Bahr–Hutton 2015**(calculation 方法论)。
5. **Reynolds 1972 + Ager et al. 2003**(defunctionalization → 抽象机)。

读完会看清:Danvy–Filinski 那句轻描淡写的 "by the standard CPS conversion" 背后,
站着的是 Stoy–Reynolds–Plotkin 的逻辑关系传统;本仓库 `src/Shift/` 的基本引理与
`src/Shift/Machine/Eval.hs` 的抽象机,正是这条传统在 shift/reset 上的两个落点。
