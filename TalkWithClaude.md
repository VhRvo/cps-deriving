User: 这里有两个 conversion 是 cps 算法, good 中的算法会引入 eta-redex, 作者说把 static continuation 消除后就能得到 OnePassTailRecursive.Conversion, 但我完全没有看懂作者的思路、思考的过程.
我又按照作者说的, 识别出 static continuation 后, 在 DerivingBetter 中,  以把 cpsC' 定义为一个专门优化过的等价形式,  经过等式推理展开后, 恰好也 OnePassTailRecursive.Conversion, 你来评价一下整体的过程.
然后你在重新顺着作者的思路, 从最朴素的 cps conversion 推导到有 eta-redex 的conversion, 再推导到没有 eta-redex 的 conversion.
论文比较老, 字复制出来可能不太对, 你需要辅以 ocr 来明确论文的细节.


GitHub Copilot: Read [](file:///Users/zhangyongzhuo/Desktop/Workplace/Languages/Haskell/cps-deriving/src/OnePassTailRecursive/ConversionWithoutEtaRedex.hs)

Read [](file:///Users/zhangyongzhuo/Desktop/Workplace/Languages/Haskell/cps-deriving/src/Expr.hs)

Read [](file:///Users/zhangyongzhuo/Desktop/Workplace/Languages/Haskell/cps-deriving/src/Plain1/Conversion.hs)

Searched for files matching `**/OnePassTailRecursive/Conversion.hs`, no matches

我先把仓库里 4 个相关版本放在一张图上对照：

| 文件 | 大致语义 | 角色 |
|---|---|---|
| Plain1/Conversion.hs | Fischer/Plotkin 朴素两遍 CPS（不消除任何 administrative redex） | 起点 |
| Good/Conversion.hs | 论文 Fig.2 的 one-pass CPS：κ 用宿主语言函数表示，在 `EApp` 分支会产生 η-redex | 中间版 |
| Good/DerivingBetter.hs | 你做的派生：定义 `cpsC' e k = cpsC e (\m -> EApp (EVar k) m)` 然后展开 | 派生过程 |
| OnePassTailRecursive/ConversionWithoutEtaRedex.hs | 论文 Fig.3 的 properly tail-recursive 版本，无 η-redex | 终点 |

---

## 一、对你 `DerivingBetter` 派生过程的评价

你做的事情等价于"把动态 continuation $k$ 提出来作为命名变量"——这正是论文 §2.6 给出的四种方案之一："把 tail-call 上下文当作继承属性，复制规则以避免动态判断"。

**规范方程**：

$$\text{cpsC'}\ e\ k \;\equiv\; \text{cpsC}\ e\ (\lambda m.\,\texttt{EApp}\ (\texttt{EVar}\ k)\ m)$$

按 `e` 归纳验证你的三个等式：

**(EVar n)** — 直接 β：
```
cpsC (EVar n) (\m -> EApp (EVar k) m)
= (\m -> EApp (EVar k) m) (EVar n)
= EApp (EVar k) (EVar n)              -- ✓ 与你写的一致
```

**(ELam n e)** — 内层 `cpsC e (\m -> EApp (EVar k') m)` 恰好就是 `cpsC' e k'`，于是递归形态保持：
```
= EApp (EVar k) (ELam n (ELam k' (cpsC' e k')))    -- ✓
```
注意这里**没有** η-redex 出现，因为外层 κ 只是把结果塞给 dynamic continuation。

**(EApp e1 e2)** — 关键步骤：
```
... EApp (EApp f arg) (ELam a ((\m -> EApp (EVar k) m) (EVar a)))
= ... EApp (EApp f arg) (ELam a (EApp (EVar k) (EVar a)))
```
此时 `ELam a (EApp (EVar k) (EVar a))` **正是一个 η-redex**（因为 `k` 是 dynamic 变量、不是任意 Haskell 函数）。你在最后一步 η-缩为 `EVar k`：
```
= cpsC e1 $ \f -> cpsC e2 $ \arg -> EApp (EApp f arg) (EVar k)    -- ✓
```

**结论**：派生完全正确，并且这正好解释了 `Good/Conversion.hs` 为什么会冒出多余 η-redex —— 因为它对**所有** κ 一视同仁地构造 `\a -> κ a`；而一旦我们知道 κ 来自顶层"把结果交给 dynamic continuation"，这层 wrapping 就立刻能 η-缩掉。

你的派生与论文 Fig.3 的关系：
- 你的 `cpsC'` ↔ 论文里的 `[[M]]'`（"properly tail-recursive" 辅助翻译）
- 你的 `cpsC` ↔ 论文里的 `[[M]]`
- 调用关系 `cpsC' (ELam ...) k = EApp (EVar k) (ELam n (ELam k' (cpsC' e k')))` 与论文方程 `[[λx.M]]' k = κ(λx.λk.[[M]]' k)` 完全一致
- `cpsC' (EApp e1 e2) k = cpsC e1 $ \f -> cpsC e2 $ \arg -> EApp (EApp f arg) (EVar k)` 与论文 `[[@M N]]' k = [[M]](λm.[[N]](λn.@(@m n) k))` 一致

唯一可以更彻底的一步：连 `EApp` 分支里递归调用的 `cpsC e1` 也可以替换成"用 dynamic continuation 调用"，但因为 `e1`/`e2` 的结果都要进一步组装成 syntax，所以**这两处必须留作 static continuation 形式**（HOAS κ），不能替换。这正是为什么 `cpsC'` 不能完全替代 `cpsC`，二者必须共存——也就是 Fig.3 里出现两套规则的根本原因。

---

## 二、按论文思路重新派生（朴素 → 含 η-redex → 无 η-redex）

下面采用论文的记号：$\overline{\lambda}/\overline{@}$ 是 **static**（翻译时执行），$\underline{\lambda}/\underline{@}$ 是 **dynamic**（出现在结果项中的语法构造子）。

### 阶段 0：Fischer/Plotkin 朴素两遍式（= `Plain1/Conversion.hs`）

$$
\begin{aligned}
[\![x]\!] &= \lambda^1\kappa.\,@^1\,\kappa\ x \\
[\![\lambda x.M]\!] &= \lambda^2\kappa.\,@^2\,\kappa\,(\lambda^3 x.\,[\![M]\!]) \\
[\![@M\ N]\!] &= \lambda^4\kappa.\,@^3\,[\![M]\!]\,(\lambda^5 m.\,@^4\,[\![N]\!]\,(\lambda^6 n.\,@^5(@^6 m\ n)\ \kappa))
\end{aligned}
$$

观察：每个 $[\![\cdot]\!]$ 的结果都是一个 $\lambda$（$\lambda^1,\lambda^2,\lambda^4$），所以 `@³ [[M]]`, `@⁴ [[N]]` 形如 `@ (λκ. ...) (...)`——**这些都是 administrative β-redex**，应该在翻译时就消掉。问题：`@¹` 不一定是 redex（当变量出现在 λ-body 里时它没人调用它），所以"是不是 redex"是 context-dependent 的。

### 阶段 1：第一次 η-展开——消除 $\lambda^{1,2,4}$ 是否 reducible 的歧义

把 $\lambda$-情形 η-展开（把 body 的隐式 continuation 显式化）：

$$[\![\lambda x.M]\!] = \lambda^2\kappa.\,@^2\kappa\,(\lambda^3 x.\,\lambda^7 k.\,@^7\,[\![M]\!]\ k)$$

这步**保持语义**，因为 $[\![M]\!]$ 永远是个 λ-abstraction（η-展开 λ 是安全的；η-展开任意 term 不安全，因为可能是发散计算）。

效果：现在每个 $[\![\cdot]\!]$ 都恰好出现在 application 的函数位置（$@^7, @^3, @^4$ 之一），它们**全都**是 administrative β-redex，可以无条件在翻译时归约。

### 阶段 2：第二次 η-展开——消除 $\kappa$ 出现位置的歧义

枚举 $\kappa$ 被绑定到什么：identifier $k$（来自 $\lambda^7$），$\lambda^5$，$\lambda^6$。前者是变量，后两个是 λ。所以"`@κ ...` 是不是 redex"又是 context-dependent。再 η-展开一次，把 continuation 的应用显式化：

$$[\![\lambda x.M]\!] = \lambda^2\kappa.\,@^2\kappa\,(\lambda^3 x.\,\lambda^7 k.\,@^7\,[\![M]\!]\,(\lambda^8 m.\,@^8\,k\,m))$$

现在所有 $\kappa$ 都被绑定到 λ，"应用 $\kappa$"都是 redex。

### 阶段 3：第三次 η-展开——消除 $@M\ N$ 里 $\kappa$ 的歧义

在 application 翻译里 $\kappa$ 作为 $@^5$ 的第二个参数出现，仍然是 dynamic 位置。再做最后一次 η-展开：

$$[\![@M\ N]\!] = \lambda^4\kappa.\,@^3\,[\![M]\!]\,(\lambda^5 m.\,@^4\,[\![N]\!]\,(\lambda^6 n.\,@^5(@^6 m\ n)\,(\lambda^9 a.\,@^9\,\kappa\,a)))$$

### 阶段 4：static/dynamic 划分（论文 Fig.2，对应 `Good/Conversion.hs`）

现在按二级 λ-演算给每个 λ/@ 标 static / dynamic：

- **Static**（翻译时归约）：$\lambda^1,\lambda^2,\lambda^4,\lambda^7,\lambda^8,\lambda^9$ 与 $@^1,@^2,@^4,@^7,@^8,@^9$
- **Dynamic**（结果项的语法构造）：$\lambda^3,\lambda^5,\lambda^6$ 与 $@^3,@^5,@^6$

把 static 部分"执行掉"（用 Haskell 函数实现 $\overline{\lambda}$），就得到 Fig.2：

$$
\begin{aligned}
[\![x]\!]\,\kappa &= \kappa\ x \\
[\![\lambda x.M]\!]\,\kappa &= \kappa\,(\underline{\lambda} x.\underline{\lambda} k.\,[\![M]\!]\,(\overline{\lambda} m.\,\underline{@}\,k\,m)) \\
[\![@M\ N]\!]\,\kappa &= [\![M]\!]\,(\overline{\lambda} m.\,[\![N]\!]\,(\overline{\lambda} n.\,\underline{@}(\underline{@}\,m\,n)\,(\underline{\lambda} a.\,\kappa\ a)))
\end{aligned}
$$

这就是 Good/Conversion.hs：
- `cpsC (ELam n e) k = k (ELam n (ELam k' (cpsC e (\m -> EApp (EVar k') m))))` ↔ 第二条
- `cpsC (EApp e1 e2) k = cpsC e1 $ \f -> cpsC e2 $ \arg -> EApp (EApp f arg) (ELam a (k (EVar a)))` ↔ 第三条

**残留问题**：`ELam a (k (EVar a))`（论文里的 $\underline{\lambda} a.\,\kappa\ a$）虽然没有 β-redex，但如果顶层 $\kappa = \overline{\lambda} m.\,\underline{@}\,k_0\,m$（即"把结果丢给某个 dynamic continuation $k_0$"），展开后就是 `ELam a (EApp (EVar k₀) (EVar a))`——一个 **η-redex**。tail-call 上每次都会产生这种 wrapper。

### 阶段 5：双套规则消除 η-redex（论文 Fig.3，对应 `ConversionWithoutEtaRedex.hs`）

η-redex 出现的充要条件是 $\kappa$ 形如 $\overline{\lambda} m.\,\underline{@}\,k\,m$（一个 dynamic continuation 变量 $k$ 的 η-wrapper）。论文的做法：把这种特殊形态的 $\kappa$ 直接传 $k$ 本身（命名形式），为之配一套独立翻译 $[\![\cdot]\!]'$：

$$
\begin{aligned}
[\![x]\!]'\,k &= \underline{@}\,k\,x \\
[\![\lambda x.M]\!]'\,k &= \underline{@}\,k\,(\underline{\lambda} x.\underline{\lambda} k'.\,[\![M]\!]'\,k') \\
[\![@M\ N]\!]'\,k &= [\![M]\!]\,(\overline{\lambda} m.\,[\![N]\!]\,(\overline{\lambda} n.\,\underline{@}(\underline{@}\,m\,n)\,k))
\end{aligned}
$$

两套翻译共存的原因：在 `[[@M N]]'` 里子项 $M,N$ 的结果还得拿来"拼装" application，它们必须用 HOAS 的 $[\![\cdot]\!]$ 才能让 $m,n$ 在 Haskell 层被引用；而 $\lambda$-body 永远在 dynamic continuation 位置，所以用 $[\![\cdot]\!]'$。

这正是 ConversionWithoutEtaRedex.hs 里 `cpsC` 与 `cpsC'` 两个互相调用的函数。**而你 DerivingBetter.hs 做的等式推理，正是从规范 `cpsC' e k = cpsC e (\m -> EApp k m)` 出发，证明这种分裂确实保持语义并自动消除了 η-redex。** 论文给出的是分类讨论（"哪里会出 η-redex，加一套规则"），你给出的是构造性派生（"先定义、再 β/η 化简到机械可计算的形式"）——两者殊途同归，且你的方式更"机械"，因为是纯粹的等式推理。

---

## 三、几点小建议

1. `cpsC'` 的第二参数类型可以是 `Expr`（如 ConversionWithoutEtaRedex.hs 那样）而不是 `Text`，这样未来如果在更复杂的扩展里需要传非变量的 continuation 也能复用。
2. 派生注释里可以加一行"$\lambda a.\,k\,a \equiv k$（η）"来突出关键化简步——这是整条派生路径上唯一非 β 的一步。

User: 这个思路是
1. 事前识别 static continuation
2. 为什么识别 \m -> EApp k m，而不是识别 ELam a (k (EVar a))
3. 作者处理的是更早一层的原因，不是处理已经生成出来的结果
4. eta-redex 是由两个东西叠加出来的
5. 原因：λa. dynK a 的直接来源就是这种 static continuation。只要把这种 static continuation 专门表示出来，就能从源头上不构造 eta-redex。

整体思路是
1. 原始 CPS:
  cps e = λk. ...
2. 发现:
  很多 (cps e) K 会产生 administrative β-redex
3. 改成:
  cpsC e kStatic
  用 Haskell 函数表示 static continuation，β-redex 在转换期消掉
4. 又发现:
  某些 kStatic = \m -> dynK m
  被 application rule residualize 后会生成 λa. dynK a
5. 继续改成:
  cpsC' e dynK
  用已有 dynamic continuation 直接表示这种特殊 static continuation
6. 结果:
  application tail position 直接生成 f arg dynK
  不再生成 f arg (λa. dynK a)

思路: 为什么会冒出多余 η-redex —— 因为它对所有 κ 一视同仁地构造 \a -> κ a；而一旦我们知道 κ 来自顶层"把结果交给 dynamic continuation"，这层 wrapping 就立刻能 η-缩掉。

请你重新、详细地分析、总结、重新推理上面三个思路,

GitHub Copilot: # 重新分析：为什么 η-redex 必须在"源头"消除

你给出的三段思路其实在讲同一件事的三个层次。我把它合成一条清晰的推理链。

---

## 核心洞察：η-redex 是两层结构"撞"出来的

`ELam a (EApp (EVar k) (EVar a))` 不是凭空冒出来的，它由**两个独立部件**叠加产生：

| 部件 | 来自 | 角色 |
|---|---|---|
| `ELam a (... (EVar a))` | `EApp` 规则**固定**的 residualization 模板 | dynamic 语法骨架 |
| `EApp (EVar k) _` | static continuation $\kappa$ 恰好是 `\m -> EApp (EVar k) m` | dynamic 内容 |

二者单独都没问题：
- 模板 `\a -> κ a` 是 `EApp` 规则的本职工作（必须有这个 dynamic λ 把 application 的返回值绑成名字）
- $\kappa = \lambda m.\ k\,m$ 也只是一种合法的 static continuation

但**当它们碰到一起**——`κ` 被代入模板——就拼成了一个 η-redex。也就是说：**η-redex 是"通用模板"与"特定 κ 形态"的乘积**。

---

## 为什么要识别 `\m -> EApp (EVar k) m`，而不是识别 `ELam a (k (EVar a))`

这是你问题里最关键的一点。两种做法对应两种修复哲学：

### 做法 A（事后修复 / 错误的思路）：识别已经生成的 `ELam a (k (EVar a))`

```haskell
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f -> cpsC e2 $ \arg ->
    let body = k (EVar a)
    in case body of
         EApp f' (EVar a') | a == a', notFree a f' -> EApp (EApp f arg) f'   -- η-缩
         _                                          -> EApp (EApp f arg) (ELam a body)
```

问题：
1. **要在结果项上做模式匹配**——离开了 syntax-directed 翻译，破坏 one-pass 性质。
2. **要做 free-variable 检查**——η-缩的合法性条件 `a ∉ FV(f')` 必须动态验证。
3. **治标**——已经构造出了那个 dynamic λ，再拆掉它意味着白做了一次构造。
4. 同样的问题在别处（如 `let`、`if` 的 join point）还会再出现，每处都得加判断。

### 做法 B（事前识别 / 论文+你的派生）：识别 `\m -> EApp (EVar k) m` 这种 static 形态

```haskell
cpsC' e k = cpsC e (\m -> EApp (EVar k) m)     -- 规范定义
```

随后用等式推理把 `cpsC'` 在每个语法构造上展开。展开到 `EApp` 时：

```
cpsC' (EApp e1 e2) k
= cpsC (EApp e1 e2) (\m -> EApp (EVar k) m)
= cpsC e1 $ \f -> cpsC e2 $ \arg ->
    EApp (EApp f arg) (ELam a ((\m -> EApp (EVar k) m) (EVar a)))   -- β
= cpsC e1 $ \f -> cpsC e2 $ \arg ->
    EApp (EApp f arg) (ELam a (EApp (EVar k) (EVar a)))             -- 暴露 η-redex
= cpsC e1 $ \f -> cpsC e2 $ \arg ->
    EApp (EApp f arg) (EVar k)                                       -- η ✓ 合法因为 a 是 fresh
```

η-缩**只在派生表里发生一次**，是开发者头脑中的化简；生成的代码 `EApp (EApp f arg) (EVar k)` 里**根本不构造那个 dynamic λ**。

优势：
1. **纯 syntax-directed**，不破坏 one-pass。
2. **不需要 free-variable 检查**——`a` 是 `genFreshName` 生成的，η-合法性在派生阶段已经被静态证明。
3. **治本**——不让 η-redex 出生。
4. 该机制可以延伸到任何"已有命名的 dynamic continuation"的场合（`let`、`if` 分支等），全都享受同一套化简。

---

## 三段思路的统一总结

把你列的三段话整合成一条递进的推理链：

### Step 1：原始 Plotkin/Fischer CPS

$$[\![e]\!] = \lambda k.\ \ldots$$

继续每一步都返回一个"等着 continuation 的 λ"。

**问题**：当 `[[e]]` 出现在 `[[@M N]]` 这种调用位置时，外层立刻拿一个 K 调用它，于是产生 `(\k. ...) K` ——**administrative β-redex**。

### Step 2：把 continuation 上提到 meta-level（→ Fig.2 / `Good/Conversion.hs`）

$$\text{cpsC} : \text{Expr} \to (\text{Expr} \to \text{Expr}) \to \text{Expr}$$

将 $\kappa$ 表示为 **Haskell 函数**（HOAS）。每次"应用 κ"在 Haskell 层立即归约，**β-redex 在翻译时就消掉，永不出现在结果中**。

但代价是：`EApp` 规则的 residual 形态写死成
```
EApp (EApp f arg) (ELam a (κ (EVar a)))
```
这里 `ELam a (κ (EVar a))` 是 **dynamic** 的，因为内层 application 必须给中间结果取一个 source-level 的名字。

### Step 3：发现 κ 的一类特殊形态会催生 η-redex

观察哪些 κ 真的会被代入 `ELam a (κ (EVar a))`：
- 来自顶层调用：`\m -> m`（恒等）—— 代入后是 `ELam a (EVar a)`，是 η-redex
- 来自外层 `EApp` 的左/右子项处理：是 Haskell 函数式 κ —— 没问题
- 来自 `ELam` body：`\m -> EApp (EVar k') m` —— 代入后是 `ELam a (EApp (EVar k') (EVar a))`，又是 η-redex

**共同特征**：这两类"会出 η-redex 的 κ"都是 `\m -> EApp dynK m` 这种"把结果转交给一个已经命名的 dynamic continuation"的形态。

### Step 4：把"特殊 κ"独立编码（→ Fig.3 / `ConversionWithoutEtaRedex.hs` / 你的 `DerivingBetter`）

既然这种 κ **本身就含有一个 dynamic continuation 名字**，不如直接用那个名字作参数：

$$\text{cpsC'} : \text{Expr} \to \text{Expr} \to \text{Expr}$$
$$\text{cpsC'}\ e\ k \;\equiv\; \text{cpsC}\ e\ (\lambda m.\,\texttt{EApp}\ k\ m)$$

现在所有"以 dynamic continuation 收尾"的位置都改调 `cpsC'`：
- 顶层调用 `cpsC' e topK`
- `ELam` body 调 `cpsC' body k'`
- `EApp` 子项**仍调 `cpsC`**（因为还要在 Haskell 层组装 application）

然后用等式推理展开 `cpsC'` 三条方程，η-redex **在符号层化简掉**，代码里再也不构造它。

### Step 5：抽象出"分层"原则

| 层 | continuation 表示 | 何时使用 |
|---|---|---|
| **元层** | Haskell 函数 `Expr -> Expr` | continuation 需要参与"构造 syntax"（如 `EApp` 子项） |
| **对象层** | dynamic 变量 `Expr`（实际是 `EVar k`） | continuation 已经是一个语法对象、只等结果代入（tail position） |

`cpsC` / `cpsC'` 的分裂本质上是把"continuation 的载体"分成两类，**而 η-redex 正是"元层载体退化为对象层载体"那一刻的产物**。提前识别这种退化，就能从源头避免。

---

## 一句话总结

> **η-redex 不是 CPS 翻译的瑕疵，而是"用通用 dynamic 模板包装一个已经命名的 dynamic continuation"这件事的必然产物。论文/你的派生没有"消除 η-redex"，而是改变了表示——让那种已被命名的 continuation 不再走通用模板，从而 η-redex 根本没有机会被构造出来。**

你的 `DerivingBetter` 用纯等式推理把这件事讲得比论文还干净：定义 → β 展开 → 显式暴露 η-redex → η-缩——四行字一气呵成地证明 Fig.3 是 Fig.2 在"κ 是 dynamic-η-wrapper"这一子情形下的特化。

User:  用纯等式推理DerivingBetter 这个思路的严密性强吗? 毕竟最后得到的是一个和之前不在相等的结果, 即如果 cpsC’ e k≡cpsC e (λm.EApp k m), cpsC' e k 不在和cpsC e (λm.EApp k m) 相等

GitHub Copilot: # 严密性分析：派生保持的是哪一种"相等"？

你的观察非常精确——这是这套派生方法里**最容易被糊弄过去**的一步。让我把它讲透。

---

## 一、明确"不再相等"的具体含义

记规范定义为
$$\text{cpsC'}_{\text{spec}}\ e\ k \;\triangleq\; \text{cpsC}\ e\ (\lambda m.\ \texttt{EApp}\ (\texttt{EVar}\ k)\ m)$$

记你最终实现的为 $\text{cpsC'}_{\text{impl}}$。在 `EApp` 分支二者输出的差别是：

| | 输出 |
|---|---|
| $\text{cpsC'}_{\text{spec}}\ (e_1\ e_2)\ k$ | `EApp (EApp f arg) (ELam a (EApp (EVar k) (EVar a)))` |
| $\text{cpsC'}_{\text{impl}}\ (e_1\ e_2)\ k$ | `EApp (EApp f arg) (EVar k)` |

把两边都看成 `Expr` 这个 Haskell ADT，它们**作为值不 `==`**——`ELam a (EApp (EVar k) (EVar a))` 与 `EVar k` 是不同的 AST 节点。所以

$$\text{cpsC'}_{\text{impl}} \;\not\equiv_{\text{Haskell}}\; \text{cpsC'}_{\text{spec}}$$

派生过程在最后一步从"等式推理"**悄悄切换到了一个更弱的等价关系**——即把输出视作 λ-演算项并取 βη-等价。

---

## 二、派生严密性的真实结构

派生其实分成两段，严密性等级不同：

### 第一段：β-展开（严密的 Haskell 等式推理）

```
cpsC' e k
= cpsC e (\m -> EApp (EVar k) m)              -- 定义
= ...                                          -- 对 e 归纳
= EApp (EApp f arg) (ELam a (EApp (EVar k) (EVar a)))
```

这一整串都是 Haskell **指称语义**层面的等式（由 β 与定义展开支持），生成的 `Expr` 值与规范完全 `==`。严密性 ✓。

### 第二段：η-化简（**离开了 Haskell 等式，进入了"被生成项的等价理论"**）

```
EApp (EApp f arg) (ELam a (EApp (EVar k) (EVar a)))
↓ "把这看作 λ-项，对它做 η-缩"
EApp (EApp f arg) (EVar k)
```

这一步**不**是 Haskell 的 `=`。它依赖一个外部断言：

> 在我们关心的"翻译正确性"意义下，`ELam a (EApp (EVar k) (EVar a))` 与 `EVar k` 可以互换。

这个断言成立**必须**附带两个前提：

1. **freshness**：`a` 不在 `EVar k` 的自由变量里。靠 `genFreshName` 保证。
2. **目标等价关系包含 η**：消费者把 `Expr` 解释为 λ-项并使用 βη-等价（或更强）作为正确性度量。

---

## 三、什么时候这一步安全，什么时候危险

### 安全：纯 λ-演算 + 目标语义是 βη-等价（论文的设定）

论文 Theorem 1：

> This equational specification computes a result **βη-equivalent** to the original Fischer/Plotkin transformation.

注意是 **βη**，不是 β，也不是语法相等。所以论文从一开始就**主动放宽**了等价关系，把 η 收进了正确性谱里。在这种语境下，最后一步合法。

### 危险：扩展到非纯 λ 时 η 不再 sound

η-缩在 call-by-value 语言里 **不一定保持语义**：

```
λa. (loop ()) a       -- 不是值，正常求值会非终止？取决于策略
loop ()               -- 立刻发散
```

更精确的版本：`λa. f a` 是一个值（lambda），`f` 可能是任意表达式；如果 `f` 是发散计算，η-缩就把"立刻发散"变成了"被调用时才发散"。论文 §2.1 那个 Remark 专门强调了这一点：

> Expanding "@f a" to "λx.@(@f a) x" is **not** in general meaning-preserving... Expanding "f" to "λx.@f x" **is** safe.

注意方向：η-**展开**安全，η-**缩**不一定。`DerivingBetter` 的最后一步是 η-缩。所以**只有当 η-展开是双向 sound 时**（即被 η-缩的位置上 `EVar k` 已经是 value、并且求值策略允许这种交换），这一步才安全。

在纯 CPS 翻译的输出里，`EVar k` 是变量，是 value，η-缩安全（论文的 §3 Lemma 3 实际给出了精确的 reduction-step 对应）。但如果你把这套派生套到 CBV 直接风格代码生成上，最后一步必须重新检查。

---

## 四、把派生改成"完全严密"的两种办法

### 办法 A：放弃语法相等，把"目标等价"显式化

承认我们要的不是 `cpsC'_impl == cpsC'_spec`，而是

$$\forall e,k.\quad \text{cpsC'}_{\text{impl}}\ e\ k \;\equiv_{\beta\eta}\; \text{cpsC'}_{\text{spec}}\ e\ k$$

这就是论文 Theorem 1 的口径。然后注释里写清"最后一步用 η"。**这是最诚实、最可读的做法**，也是论文的做法。

### 办法 B：把 η 推到"虚拟项"里，保持 Haskell 层 ≡

引入一个 smart constructor：
```haskell
smartLam a (EApp f (EVar a')) | a == a', a `notElem` freeVars f = f
smartLam a body = ELam a body
```

然后让 `cpsC` 用 `smartLam` 取代裸的 `ELam`。这样 `cpsC'_spec e k` 直接 reduce 到 `EVar k`，Haskell 层完全 `==`。代价：把 η 隐藏到 smart constructor 里，运行时还是做了 free-variable 检查（违背了"事前消除"的初衷）。

### 办法 C：用 normalization-by-evaluation 类型的语义证明

把目标域换成"项的 βη-等价类"而非 `Expr` 值本身。Sabry-Felleisen 1992 之后的一系列工作正是这条路。

---

## 五、对你 `DerivingBetter` 这份代码的判定

| 维度 | 评价 |
|---|---|
| β-展开部分 | **严密**，纯 Haskell 等式 |
| η-缩那一步 | **非语法等式**，依赖 (1) freshness (2) βη-等价为目标 |
| 在论文设定下 | **合法**，与论文 Theorem 1 同口径 |
| 是否需要补论证 | 应该在 `EApp` 分支注释里**显式**写出最后一步是 η，并附 freshness 条件 |
| 实际正确性 | ✓（`a` 由 `genFreshName` 保证 fresh，且 `EVar k` 永远是 value） |

**一句话**：派生在 Haskell 层做到了 95% 的严密，剩下 5% 是一次有意的、受 freshness 保护的、被论文目标等价（βη）所授权的 η-化简。它不是"等式推理崩了"，而是"等式推理算到这里之后，剩下的事交给了 λ-演算的 η 规则"。诚实的做法是把这次交接**写在注释里**，不要让读者以为整套是 Haskell 的 `=`。

可以加这样一行注释让派生过程闭环：

```haskell
cpsC' (EApp e1 e2) k =
  -- ... (β-展开到这里得到:)
  -- cpsC e1 $ \f -> cpsC e2 $ \arg ->
  --   EApp (EApp f arg) (ELam a (EApp (EVar k) (EVar a)))
  --
  -- 最后一步：η-缩 `\a -> k a` ⇝ `k`
  --   合法性条件：a ∉ FV(EVar k)，由 genFreshName 保证
  --   等价层级：从 Haskell 语法相等放宽为目标项的 βη-等价（同论文 Thm 1）
  cpsC e1 $ \f -> cpsC e2 $ \arg ->
    EApp (EApp f arg) (EVar k)


User: 详细说一下: 为什么会冒出多余 η-redex —— 因为它对所有 κ 一视同仁地构造 \a -> κ a；而一旦我们知道 κ 来自顶层"把结果交给 dynamic continuation"，这层 wrapping 就立刻能 η-缩掉。

GitHub Copilot: # 详解：`\a -> κ a` 这个 wrapping 为什么出现、何时变成多余

我把这句话拆成四个递进的问题来回答：

1. `\a -> κ a` 这个 wrapping **为什么必须存在**？
2. 它在 κ 是**任意 Haskell 函数**时是不是多余？
3. 它在 κ 是**`\m -> EApp dynK m` 这种特殊形态**时**为什么**变成 η-redex？
4. 提前识别这种 κ 形态，**为什么**就能从源头不构造这个 wrapping？

---

## 一、`\a -> κ a` 为什么必须存在

回看 `Good/Conversion.hs` 的 `EApp` 规则：

```haskell
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->
    cpsC e2 $ \arg ->
      let a = genFreshName "a"
       in EApp (EApp f arg) (ELam a (k (EVar a)))
```

CPS 翻译 `@e₁ e₂` 的运行时含义是：

> "先求出 `e₁`，再求出 `e₂`，把二者应用得到结果 `v`，最后把 `v` 交给当前 continuation。"

最后一步"把结果交给 continuation"在 CPS 项里就是把 continuation **作为一个 dynamic 值**塞到 application 的第三个槽里：

```
f arg <continuation>
       ^^^^^^^^^^^^^
       这里需要一个 source-level 的 Expr，
       它接受一个参数（运行时才产生的结果 v）并继续计算
```

但 κ 是 **Haskell 函数** `Expr -> Expr`，它**不是**一个 `Expr`，不能直接塞进 `EApp` 的槽里。要把"Haskell 层的 κ"变成"对象层的 continuation"，唯一的通用办法是：

1. 生成一个 fresh 变量 `a`
2. 在 κ 里把这个变量当作"未来才会到来的结果"代入，得到 body `κ (EVar a)`
3. 用 `ELam a` 把 body 抽象起来 → `ELam a (κ (EVar a))`

这就是 **reification**——把 meta-level 函数 reify 成 object-level lambda。`ELam a (κ (EVar a))` 是 reification 的**唯一通用模板**，不可避免。

---

## 二、当 κ 是任意 Haskell 函数时，这个 wrapping 不是多余

举两个例子。

**例 A**：κ 是顶层调用传入的恒等
```haskell
cpsC (EApp (EVar "f") (EVar "x")) (\m -> m)
```
代入模板：
```
EApp (EApp (EVar "f") (EVar "x")) (ELam a (EVar a))
                                    ^^^^^^^^^^^^^^^^
                                    恒等函数的 reification，没法再小了
```
这里 `ELam a (EVar a)` 已经是 normal form，**不可消除**（除非用 `Iₛ` 这种 combinator，但那超出对象语言）。

**例 B**：κ 来自外层 `EApp` 的处理
```haskell
cpsC (EApp e1 e2) (\m -> EApp m (EVar "y"))
```
代入模板：
```
EApp (EApp f arg) (ELam a (EApp (EVar a) (EVar "y")))
                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                   这是一个真实需要的 dynamic λ：
                   它把 application 的结果 a 再次 apply 到 y
```
这里 `EApp (EVar a) (EVar "y")` 实质性地用到了 `a`，**不是** η-redex，**不可消除**。

**结论**：对任意 κ，`ELam a (κ (EVar a))` 是必要的、通用的、不可省的 reification 模板。

---

## 三、当 κ = `\m -> EApp (EVar dynK) m` 时，为什么变成 η-redex

`cpsC' e dynK` 的定义恰好把 κ 固定成这一形态：

```
κ ≡ \m -> EApp (EVar dynK) m
```

代入通用模板：

```
ELam a (κ (EVar a))
= ELam a ((\m -> EApp (EVar dynK) m) (EVar a))     -- 把 κ 写开
= ELam a (EApp (EVar dynK) (EVar a))               -- β-缩 meta-level
```

得到的结果 `ELam a (EApp (EVar dynK) (EVar a))` 是一个**纯粹的 object-level η-redex**：

- 它的 body 形如 `EApp f (EVar a)`
- `f = EVar dynK` 不含 `a`（因为 `a` 是 fresh）
- 满足 η-缩的所有条件，η-缩之后等于 `EVar dynK`

**直观图示**：

```
  通用模板:    \a -> [   ?   ] a       ← reification wrapping
   特殊 κ:           EVar dynK         ← κ 内层已经是 "应用某个 dynamic 变量"
   合成:       \a -> EVar dynK a       ← 两层 "应用 dynK" 撞在一起
                ^^^^^^^^^^^^^^^^^^^
                这就是 η-redex
```

可以把它看作**两层 plumbing 的撞车**：
- 模板提供的外层 plumbing：`\a -> [_] a`（把对象层结果接进 meta-level κ）
- κ 自己的内层 plumbing：`\m -> dynK m`（把 meta-level 结果接给对象层 dynK）

二者在 `a` 这个 fresh 变量处汇合，组成"先 wrap 再 unwrap"——典型的 η-redex。**单独看任一层都没问题，撞在一起才冗余。**

---

## 四、为什么"提前识别"就能从源头不构造 wrapping

关键在于：**reification 模板只在我们"需要把 meta-level κ 变成 object-level continuation"时才有用**。

如果我们一开始就知道 continuation 已经是 object-level 的（也就是 dynamic 变量 `dynK`），那根本**不需要 reify**——直接把 `EVar dynK` 塞进 `EApp` 的槽里就行。

这就是 `cpsC' e dynK` 的设计：

```haskell
cpsC' :: Expr -> Var -> Expr
--                ^^^
--                第二个参数直接是 dynamic continuation 的名字，
--                不是 Haskell 函数，根本没有 "Haskell→Expr" 的鸿沟要跨
```

`cpsC'` 的 `EApp` 规则因此可以直接写：

```haskell
cpsC' (EApp e1 e2) k =
  cpsC e1 $ \f ->                     -- 子项 e1 的结果还要在 meta-level 组装，
                                      -- 所以这里仍用 cpsC（Haskell 函数 κ）
    cpsC e2 $ \arg ->
      EApp (EApp f arg) (EVar k)      -- continuation 槽直接放 EVar k，
                                      -- 没有 ELam a (...)，没有 fresh 变量
```

对比一下两种实现在 `EApp` 分支生成的代码：

| 实现 | continuation 槽生成的代码 | 是否有 wrapping |
|---|---|---|
| `cpsC (EApp _ _) (\m -> EApp (EVar k) m)` | `ELam a (EApp (EVar k) (EVar a))` | 有，且是 η-redex |
| `cpsC' (EApp _ _) k` | `EVar k` | 无 |

`cpsC'` **根本没有走 reification 这条路**，所以 wrapping 不存在；既然 wrapping 不存在，η-redex 自然也不存在。

---

## 五、一句话总结

> **`\a -> κ a` 这个 wrapping 是 "把 meta-level 函数 reify 成 object-level lambda" 的通用模板，对一般的 κ 它是必要的；但当 κ 本身已经是 "把结果转交给某个 dynamic continuation `k`" 这种形态时，它内层已经有一份 `k _`，与模板外层的 `\a -> _ a` 撞出 η-redex。提前识别这种 κ、改用 `cpsC' e k` 直接以 dynamic 变量为参数，就跳过了 reification 步骤，从源头让 wrapping 不被构造。**

换言之：**η-redex 是 reification 的副产品；只要在不需要 reification 的场合避免触发它，η-redex 就不会被生出来。**

User: 说一下, 一旦我们知道 κ 来自顶层"把结果交给 dynamic continuation"，这层 wrapping 就立刻能 η-缩掉, 和 tail-context 的关系

GitHub Copilot: # "κ 来自把结果交给 dynamic continuation" 与 tail-context 的关系

这两个说法其实是**同一件事的两种讲法**：一种从"continuation 的形态"切入，一种从"被翻译子项在源程序里的语法位置"切入。下面把这层等价讲透。

---

## 一、回顾两个概念

### Tail-context（尾位置上下文）

一个子项 `e` 处于 tail position，意思是：**`e` 求得的值就是包围它的"最近一层有名字的 continuation"想要的值，中间没有任何额外计算需要插进来**。

直接风格里典型的 tail position：
- 整个程序的顶层 `e`（结果交给 toplevel continuation）
- 函数体：`λx. e` 中的 `e`（结果交给"调用者传进来的 continuation"）
- `let x = ... in e` 的 body `e`
- `if p then e₁ else e₂` 的两个分支
- **`@e₁ e₂` 中的 `e₁`、`e₂` 不是 tail position**（它们的结果还要参与一次 application 才能交给外层 continuation）

### "κ 来自顶层把结果交给 dynamic continuation"

意思是：当前调用 `cpsC e κ` 时，`κ` 恰好形如
```
κ = \m -> EApp (EVar k) m
```
即"拿到结果就立刻喂给某个已命名的 dynamic 变量 `k`，不做任何别的事"。

---

## 二、二者其实是同义反复

我们逐个查看 `cpsC e κ` 被调用的所有上下文，看 κ 的形态与 `e` 的位置之间的对应：

### 调用点 1：顶层
```haskell
cpsC e (\m -> EApp (EVar topK) m)   -- 顶层把结果送给 topK
```
- κ 是"裸的 dynamic wrapper" ✓
- `e` 是顶层表达式，**在 tail position** ✓

### 调用点 2：`ELam` 规则
```haskell
cpsC (ELam n e) k =
  let k' = genFreshName "k"
   in k (ELam n (ELam k' (cpsC e (\m -> EApp (EVar k') m))))
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```
- κ 是 `\m -> EApp (EVar k') m`，dynamic wrapper ✓
- `e` 是 lambda body，**在 tail position** ✓

### 调用点 3：`EApp` 规则
```haskell
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f ->            -- κ = \f -> cpsC e2 (\arg -> EApp (EApp f arg) ...)
    cpsC e2 $ \arg ->        -- κ = \arg -> EApp (EApp f arg) ...
      EApp (EApp f arg) (ELam a (k (EVar a)))
```
- 这里两个 κ 都**不是**裸 dynamic wrapper：第一个 κ 还要继续翻译 `e2`，第二个 κ 还要构造 `EApp (EApp f arg) _`
- `e1`、`e2` 都**不在 tail position** ✓

**完美对应**：

> **κ 形如 `\m -> EApp (EVar k) m`** ⟺ **被翻译的子项 `e` 在源程序的 tail position**

为什么必然如此？因为 κ 描述的就是"这个子项的结果出来后**还要做什么**"。如果还要做的事**只是"送给某个 continuation"**（即 dynamic wrapper），那本就是 tail position 的定义；如果还要做别的（先 apply、先 case、先 +1…），那就不是 tail position。

---

## 三、tail-context 视角下的 η-redex 来源

把上面的对应关系代回到 `EApp` 规则：

```haskell
EApp (EApp f arg) (ELam a (k (EVar a)))
```

只有当 κ 是 dynamic wrapper（即 `EApp e₁ e₂` 这整个 application **本身**处在 tail position）时，`ELam a (κ (EVar a))` 才会展开成 η-redex `ELam a (EApp (EVar k) (EVar a))`。

也就是说：

> **η-redex 出现的位置 = source program 里的"tail call"**

正因如此论文 §2.6 才把这一节命名为 **"Tail-calls and η-redexes"**——副产品 η-redex 与 tail-call 是同一现象。例子：

源程序：`λf. f x` （`f x` 是 tail call）

`Good/Conversion.hs` 输出（保留 η-redex）：
```
λf. λk. (f x) (λa. k a)
                ^^^^^^^
                η-redex，正对应 tail position 的 f x
```

ConversionWithoutEtaRedex.hs 输出（消除）：
```
λf. λk. (f x) k
                ^
                直接传 k——这正是 "properly tail-recursive" 的定义
```

---

## 四、为什么 `cpsC' e k` 等价于"翻译 tail 位置的 e"

`cpsC'` 接受一个**对象层** continuation `k :: Var`，规范定义是

$$\text{cpsC'}\ e\ k \;\equiv\; \text{cpsC}\ e\ (\lambda m.\ \texttt{EApp}\ k\ m)$$

按上面的对应，右边正是"翻译一个 tail position 的子项 `e`，其结果送给 dynamic continuation `k`"。所以 `cpsC'` 实际上是一个**专门处理 tail-position 子项**的 CPS 翻译器。

这也解释了 `Fig.3` 双套规则的分工：

| 函数 | 处理的子项位置 | continuation 表示 | 是否构造 reification wrapping |
|---|---|---|---|
| `cpsC` | 非 tail（`EApp` 的子项） | meta-level `Expr -> Expr` | 需要（一般 κ 必须 reify） |
| `cpsC'` | tail（顶层、`ELam` body、tail-call 本身） | object-level `Var` | 不需要（continuation 已经是 syntax） |

`cpsC'` 三条方程里 continuation 都直接以 `EApp (EVar k) _` / `(EVar k)` 形式出现在结果中——**这正是 tail-recursive 调用的语法形式**：

```haskell
cpsC' (EVar n) k     = EApp (EVar k) (EVar n)                              -- tail return
cpsC' (ELam n e) k   = EApp (EVar k) (ELam n (ELam k' (cpsC' e k')))       -- tail return value
cpsC' (EApp e1 e2) k = cpsC e1 $ \f -> cpsC e2 $ \arg ->
                         EApp (EApp f arg) (EVar k)                         -- tail call
```

---

## 五、术语连贯起来的图景

```
┌────────────────────────────────────────────────────────────────────────┐
│ 源程序结构                                                              │
│   tail position ──────────► non-tail position                          │
│       e (顶层)                @e₁ e₂ 里的 e₁, e₂                         │
│       ELam x. e               primitive 操作的参数                       │
│       let _ = _ in e          case scrutinee                          │
└─────────┬─────────────────────────────┬────────────────────────────────┘
          │                             │
          ▼                             ▼
   continuation 是 dynamic         continuation 是 meta-level
   "wrapping" 形态 \m -> k m       Haskell 函数，要做实际拼装
          │                             │
          ▼                             ▼
   用 cpsC' e k 翻译              用 cpsC e κ 翻译
   (Fig.3 的 [[·]]')              (Fig.2 的 [[·]])
          │                             │
          ▼                             ▼
   结果项里的 continuation 槽         结果项里的 continuation 槽
   直接是 EVar k                    必须 reify 成 ELam a (κ (EVar a))
   (无 η-redex)                     (一般是 dynamic λ；若 κ 恰好是
                                    wrapping 形态则会出 η-redex)
```

---

## 六、一句话总结

> **tail-context 和 "κ 来自把结果交给 dynamic continuation" 是同一现象的两个名字：前者描述的是源程序里"还要做什么"为空的语法位置，后者描述的是翻译过程中那一刻 continuation 退化成"只是命名传递"的形态。这两种情形完全重合，正因如此 η-redex 总是出现在 tail call 上、且通过把 tail-position 子项分派给 `cpsC'`（即论文里的 `[[·]]'`）就能彻底消除——这就是论文给这套机制起名 "properly tail-recursive" 的根本原因。**

User: 你提到了 reification, 这个 reification 是什么? 和 normalization by evaluation 里面的 reification 有什么关系? 和 Partial Evaluation 有什么关系?

GitHub Copilot: # Reification 的三个层次：CPS / NbE / Partial Evaluation

这三处出现的 "reification" 不是巧合——它们其实是**同一个抽象操作在三种不同语境下的实例化**。我从 CPS 开始，逐步抽象到一般概念，再落回到 NbE 与 PE。

---

## 一、Reification 的一般定义

> **Reification** = 把一个"在 meta-level（宿主语言）里存在的语义对象"转换成"在 object-level（被翻译/被解释的语言）里可见的语法对象"。

关键词：**meta → object**、**semantic → syntactic**、**implicit → explicit**。

它的对偶叫 **reflection**（也叫 **eval**）：object → meta，把语法对象嵌入回宿主语义。

| 方向 | 名字 | 类型示意 |
|---|---|---|
| meta → object | reify / quote | `Sem τ → Expr τ` |
| object → meta | reflect / eval | `Expr τ → Sem τ` |

reify/reflect 在不同的 `Sem` 选择下，就化身为不同领域里的不同名词。

---

## 二、CPS 翻译里的 reification

我们之前看到的 `EApp` 规则：

```haskell
cpsC (EApp e1 e2) k =
  cpsC e1 $ \f -> cpsC e2 $ \arg ->
    let a = genFreshName "a"
     in EApp (EApp f arg) (ELam a (k (EVar a)))
                          ^^^^^^^^^^^^^^^^^^^^^^
                          reify k :: (Expr -> Expr) → Expr
```

这里发生的 reification 是：

```
reify : (Expr → Expr) → Expr           -- meta function → object lambda
reify κ = ELam a (κ (EVar a))         where a fresh
```

它的 inverse（reflect）是：

```
reflect : Expr → (Expr → Expr)         -- object expression → meta function
reflect e = \v -> EApp e v
```

注意 `reflect e v = EApp e v` 在 meta-level **真的就**是 `\v -> EApp e v`——一个 Haskell function。

复合起来：

```
reify (reflect e)
= ELam a (reflect e (EVar a))
= ELam a (EApp e (EVar a))
= η-redex (假设 a ∉ FV(e))
```

**这就是 η-redex 的来源**：`reify ∘ reflect = ELam a. EApp _ (EVar a)`，正是 η-expansion 算子。每当 κ 形如 `reflect dynK`（也就是 `\m -> EApp (EVar dynK) m`）时，`reify κ` 就把它"还原成"η-展开形式 `ELam a (EApp (EVar dynK) (EVar a))`——一个等待被 η-缩的 redex。

`cpsC'` 的本质就是**跳过 `reflect`**：既然 continuation 一开始就是对象层 `Var`，那就直接把它放进 `EApp` 槽，不必先 reflect 成 meta function 再 reify 回去。

---

## 三、Normalization by Evaluation 里的 reification

NbE 的目标：给定一个语法项 `e :: Expr τ`，返回它的 βη-normal form。算法是：

```
nf : Expr τ → Expr τ
nf = reify ∘ eval
```

其中：
- `eval : Expr τ → Sem τ` 把语法项跑成一个**宿主语言里的 semantic value**
- `reify : Sem τ → Expr τ` 再把这个 semantic value 写回为**已经处于 normal form** 的语法项

`Sem` 在 NbE 里通常是 **type-indexed** 的，最经典的定义（对 simply-typed lambda）：

```
Sem base       = Expr base                                  -- 神经/原子项
Sem (σ → τ)   = Sem σ → Sem τ                              -- meta-level 函数
```

reify 必须知道类型才能正确递归：

```
reify {base}    : Expr base   → Expr base     = id
reify {σ → τ}  : (Sem σ → Sem τ) → Expr (σ→τ)
reify {σ → τ}  f = ELam x (reify {τ} (f (reflect {σ} (EVar x))))
                                                where x fresh
reflect {base}   : Expr base → Sem base       = id
reflect {σ → τ} : Expr (σ→τ) → (Sem σ → Sem τ)
reflect {σ → τ} e = \v -> reflect {τ} (EApp e (reify {σ} v))
```

**与 CPS reification 的对应**：

| | CPS 里的 reify | NbE 里的 reify（函数型） |
|---|---|---|
| 签名 | `(Expr → Expr) → Expr` | `(Sem σ → Sem τ) → Expr (σ→τ)` |
| 公式 | `\κ → ELam a (κ (EVar a))` | `\f → ELam x (reify (f (reflect (EVar x))))` |
| fresh 变量 | 是 | 是 |
| 复合 reify∘reflect | 产生 η-redex（如果再 η-缩则 = id 在 normal-form 上） | **恰好等于 identity（normal form 里 reify∘reflect 不再产生 redex）** |

NbE 的精彩之处在于：通过给 `Sem (σ→τ)` 用 meta-level 函数表示，所有 β-redex **在 `eval` 时自动消掉**（meta-level β），而 reify 在写回时**自动做 η-expand**，结果正好是 **β-normal η-long form**。

**CPS 的 `cpsC` 用 HOAS 表示 κ，本质上就是把 continuation 这条 "answer" 通道做了一次小型 NbE**：meta-level β 在翻译时消掉（消除 administrative redex），最后 reify 时可能引入冗余 η。`cpsC'` 的优化等价于"identity reify"：当 `Sem σ` 已经就是 `Expr σ` 时不必走 reify∘reflect。

---

## 四、Partial Evaluation 里的 reification

PE 的核心数据结构是 **two-level lambda calculus**：每个 λ/@ 都被标注为 **static**（`λ̄`/`@̄`，翻译/specialization 时执行）或 **dynamic**（`λ`/`@`，进入残留程序）。

PE 的关键操作叫 **residualization**：当一段已经"半计算"的代码必须被冻成残留代码时，要把它里面所有 static 的高阶值变成 dynamic 语法。这个动作就是 reification。

类型上：
```
Static value :: 宿主语言里的某种东西（函数、数据、…）
Dynamic code :: Expr
residualize / lift : Static → Dynamic    -- 这就是 reify
```

具体到函数型 static value：

```
lift {σ → τ} : (Static σ → Static τ) → Expr (σ → τ)
lift {σ → τ} f = ELam x (lift {τ} (f (Dyn (EVar x))))
                                          where x fresh
```

——**和 NbE 的 reify 一模一样**。区别只在于：

| | NbE | PE |
|---|---|---|
| 起点 | 已有源项 `e`，先 `eval` 得到 `Sem` | 源项已经被分阶（static/dynamic 标注），specializer 边走边计算 static、边累积 dynamic |
| 终点 | β-normal η-long form | residual program |
| 触发 reify 的时机 | 最后做 `nf = reify ∘ eval` | 任何"static 值要被嵌入 dynamic 上下文"时（如出现在 dynamic application 的参数位） |

Danvy & Filinski 这篇论文的副标题观点正是：**一遍 CPS 翻译就是一次 partial evaluation**，源语言里的"administrative 部分"被标注为 static、"essential 部分"标注为 dynamic：

```
[[x]]   = λ̄κ. @̄ κ x                    -- 全 static
[[λx.M]] = λ̄κ. @̄ κ (λ x. λ k. @̄ [[M]] (λ̄m. @ k m))
                     ^         ^^^^^^^^^^^^^^^^^^^
                     dynamic   static
[[@M N]] = λ̄κ. @̄ [[M]] (λ̄m. @̄ [[N]] (λ̄n. @ (@ m n) (λ a. @̄ κ a)))
                                                       ^^^^^^^^^^^
                                                       这里把 static κ 
                                                       residualize 成
                                                       dynamic λa. ...
```

最后那个 `λ a. @̄ κ a`：外层 `λ a.` 是 **dynamic** 的（要进入残留项），但 body 里的 `@̄ κ a` 是 **static** 的（κ 是 static 函数，立刻调用）。这一步恰恰就是 **lift / reify κ**——把 static 函数 κ 在 dynamic application 的参数位嵌入回来。

η-redex 出现的条件再翻译一遍：

> 当被 reify 的 static 函数 κ 内层**已经是一次 dynamic application** `λ̄m. @ k m`，外层 reify 又包了一层 `λ a. _ a`，二者撞成 η-redex。

这与之前"两层 plumbing 撞在一起"的描述完全一致，只是术语换成了 PE 的语言。

---

## 五、三者的统一图景

```
                   ┌──────────────────────┐
                   │   reify : Sem → Expr │   把"语义对象"写成"语法对象"
                   │   reflect : Expr → Sem│   把"语法对象"嵌入语义
                   └──────────────────────┘
                            ↓ 实例化
   ┌─────────────────────┬──────────────────────┬─────────────────────┐
   │   CPS one-pass      │        NbE           │   Partial Evaluation │
   ├─────────────────────┼──────────────────────┼─────────────────────┤
   │ Sem = Expr→Expr     │ Sem (σ→τ)=Sem σ→Sem τ│ Static value (任意)  │
   │ 表示 continuation   │ 表示 simply-typed 项 │ 表示已知的 static 部分 │
   │                     │                      │                     │
   │ reify κ =           │ reify f =            │ lift f =            │
   │   ELam a (κ (EVar a))│   ELam x (reify     │   ELam x (lift      │
   │                     │     (f (reflect      │     (f (Dyn         │
   │                     │       (EVar x))))    │       (EVar x))))   │
   │                     │                      │                     │
   │ 触发点：EApp 的     │ 触发点：nf = reify   │ 触发点：static 值要 │
   │   continuation 槽   │       ∘ eval         │   进入 dynamic 上下文 │
   │                     │                      │                     │
   │ 副产品 η-redex 来源：│ 自动 η-long 不冗余： │ 副产品 η-redex 与 CPS│
   │   reify ∘ reflect    │   reify ∘ reflect    │   同源（CPS 是 PE 的 │
   │   = η-expansion      │   = id on nf         │   一个实例）          │
   └─────────────────────┴──────────────────────┴─────────────────────┘
```

三件事的内在统一：
- **NbE = "用 reify/reflect 做 normalization"**
- **PE = "用 reify/reflect（+ binding-time analysis）做 staged 计算"**
- **One-pass CPS = "把 continuation 看作 static、把语法构造看作 dynamic 的 PE"**

`Good` 和 `OnePassTailRecursive` 两份代码的差别，在 PE/NbE 语言里就是：

| | 做了什么 reify |
|---|---|
| `Good/Conversion.hs` | 任何 continuation 进 `EApp` 槽都强制 `reify`，对 `reflect dynK` 这种 κ 会产生 `reify ∘ reflect = η-expansion` 副产物 |
| `OnePassTailRecursive/ConversionWithoutEtaRedex.hs` | 区分 "continuation 已经是 dynamic 名字" 和 "continuation 是 static 函数"，前者**短路**不走 reify；等价于 NbE 在 `Sem base = Expr base` 那一支用 `reify = id` |

---

## 六、一句话总结

> **CPS 翻译里的 reification、NbE 里的 reify、PE 里的 residualize，本质上是同一个 `meta → object` 转换。每当一个"宿主层函数 κ"必须被写回为"对象层 λ"时，就需要 reify；每当 κ 内部其实只是 reflect 了一个已存在的对象层值时，`reify ∘ reflect` 就产生 η-redex。`cpsC'` / Fig.3 / Properly tail-recursive 这条优化，等价于在对象-语义恒同的子情形下省掉 reify∘reflect——这也是 NbE 里"`Sem base = Expr base` 让 base 类型上 reify=reflect=id" 这条朴素观察的 CPS 版翻译。**

如果你想继续往下挖，**Danvy 后续的两条研究线**正好对应这两端：
- **"Type-directed partial evaluation" (Danvy 1996)**：把 NbE 直接当 PE 用，reify/reflect 由类型驱动。
- **"A functional correspondence between evaluators and abstract machines" (Ager–Biernacki–Danvy–Midtgaard 2003)**：用 CPS + defunctionalization 在 NbE 与 abstract machine 之间建立一一对应，reification 是其中关键步骤。
