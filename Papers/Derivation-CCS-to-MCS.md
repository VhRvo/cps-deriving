# 从 CCS 到 MCS:逻辑关系基本引理与抽象机

本文沉淀 `src/Shift/` 的核心理论:如何把 **continuation-composing style (CCS)** 的
shift/reset 语义,经 standard CPS conversion 得到 **meta-continuation semantics (MCS)**,
并用**逻辑关系 (logical relation)** 证明二者一致;以及对 MCS 做 defunctionalization
得到的抽象机([src/Shift/Machine/Eval.hs](../src/Shift/Machine/Eval.hs))。

文献谱系见 [Papers/References.md](References.md)。

---

## 0. 类型(一切的起点)

CCS 的答案类型就是值类型 `Ans_c = Val`,于是

$$
\mathrm{Cont}_c=\mathrm{Val}\to\mathrm{Val},\qquad
\mathrm{Proc}_c=\mathrm{Val}\to\mathrm{Cont}_c\to\mathrm{Val}.
$$

continuation 能复合 $\kappa'(\kappa\,v)$,正因为 $\kappa v:\mathrm{Val}$ 又能喂给 $\kappa'$ —— 这就是
"continuation-composing" 的字面含义。

MCS 把真答案类型 $\mathrm{Ans}$ 拆出来,用 meta-continuation $\gamma:\mathrm{Val}\to\mathrm{Ans}$
搬运:

$$
\mathrm{MCont}=\mathrm{Val}\to\mathrm{Ans},\quad
\mathrm{Cont}_{mc}=\mathrm{Val}\to\mathrm{MCont}\to\mathrm{Ans},\quad
\mathrm{Proc}_{mc}=\mathrm{Val}\to\mathrm{Cont}_{mc}\to\mathrm{MCont}\to\mathrm{Ans}.
$$

congruence $\mathcal{E}_{mc}\rho\kappa\gamma=\gamma(\mathcal{E}_c\rho\kappa)$ 类型通,因为
$\mathcal{E}_c\rho\kappa:\mathrm{Val}$ 而 $\gamma:\mathrm{Val}\to\mathrm{Ans}$。

---

## 1. 两套语义方程

$$
\begin{array}{l|l}
\textbf{CCS } \mathcal{E}_c & \textbf{MCS } \mathcal{E}_{mc}\\\hline
\mathcal{E}_c[\![x]\!]\rho\kappa=\kappa(\rho x) & \mathcal{E}_{mc}[\![x]\!]\rho\kappa\gamma=\kappa(\rho x)\gamma\\
\mathcal{E}_c[\![\lambda x.E]\!]\rho\kappa=\kappa(\lambda v\kappa'.\mathcal{E}_c[\![E]\!]\rho[x{\mapsto}v]\kappa') & \mathcal{E}_{mc}[\![\lambda x.E]\!]\rho\kappa\gamma=\kappa(\lambda v\kappa'\gamma'.\mathcal{E}_{mc}[\![E]\!]\rho[x{\mapsto}v]\kappa'\gamma')\gamma\\
\mathcal{E}_c[\![E_1E_2]\!]\rho\kappa=\mathcal{E}_c[\![E_1]\!]\rho(\lambda f.\mathcal{E}_c[\![E_2]\!]\rho(\lambda a.f\,a\,\kappa)) & \mathcal{E}_{mc}[\![E_1E_2]\!]\rho\kappa\gamma=\mathcal{E}_{mc}[\![E_1]\!]\rho(\lambda f\gamma_1.\mathcal{E}_{mc}[\![E_2]\!]\rho(\lambda a\gamma_2.f\,a\,\kappa\,\gamma_2)\gamma_1)\gamma\\
\mathcal{E}_c[\![\xi k.E]\!]\rho\kappa=\mathcal{E}_c[\![E]\!]\rho[k{\mapsto}\lambda v\kappa'.\kappa'(\kappa v)]\,(\lambda x.x) & \mathcal{E}_{mc}[\![\xi k.E]\!]\rho\kappa\gamma=\mathcal{E}_{mc}[\![E]\!]\rho[k{\mapsto}\lambda v\kappa'\gamma'.\kappa\,v\,(\lambda w.\kappa'\,w\,\gamma')]\,(\lambda x\gamma''.\gamma''x)\,\gamma\\
\mathcal{E}_c[\![\langle E\rangle]\!]\rho\kappa=\kappa(\mathcal{E}_c[\![E]\!]\rho(\lambda x.x)) & \mathcal{E}_{mc}[\![\langle E\rangle]\!]\rho\kappa\gamma=\mathcal{E}_{mc}[\![E]\!]\rho(\lambda x\gamma'.\gamma'x)\,(\lambda v.\kappa\,v\,\gamma)
\end{array}
$$

(`if` 略,见正文)。

---

## 2. 逻辑关系

按域结构归纳定义。$\sim_V$ 在基本值上是相等,在过程上是 $\sim_P$。

$$
\begin{aligned}
\kappa_{mc}\sim_K\kappa_c &\iff \forall v_{mc}\sim_V v_c,\ \forall\gamma\ \text{尊重}\ \sim_V:\ \kappa_{mc}\,v_{mc}\,\gamma=\gamma(\kappa_c\,v_c)\\
p_{mc}\sim_P p_c &\iff \forall v_{mc}\sim_V v_c,\ \forall\kappa_{mc}\sim_K\kappa_c,\ \forall\gamma:\ p_{mc}\,v_{mc}\,\kappa_{mc}\,\gamma=\gamma(p_c\,v_c\,\kappa_c)\\
\rho_{mc}\sim_E\rho_c &\iff \forall x:\ \rho_{mc}x\sim_V\rho_c x\\
M_{mc}\sim_C M_c &\iff \forall\gamma\ \text{尊重}\ \sim_V:\ M_{mc}\,\gamma=\gamma(M_c)
\end{aligned}
$$

**$\gamma$ 尊重 $\sim_V$**(= 逻辑关系在 MCont 类型的对角线):
$v_{mc}\sim_V v_c\Rightarrow\gamma\,v_{mc}=\gamma\,v_c$。
它在**可观测答案类型**上自动成立(过程不逃逸为最终答案),且证明中构造的每个 $\gamma$ 都对它封闭。

> 这四个关系就是六条改写规则的本体:R-κ = $\sim_K$,R-Proc = $\sim_P$,R-Comp = $\sim_C$,
> if-distrib = $\gamma$ 与 meta-`if` 的交换。**规则数 = 域里类型构造子数。**

---

## 3. 基本引理(Fundamental Lemma)

> **定理.** 若 $\rho_{mc}\sim_E\rho_c$ 且 $\kappa_{mc}\sim_K\kappa_c$,则对所有尊重 $\sim_V$ 的 $\gamma$:
> $$\mathcal{E}_{mc}[\![E]\!]\rho_{mc}\kappa_{mc}\gamma=\gamma\big(\mathcal{E}_c[\![E]\!]\rho_c\kappa_c\big).$$
> 这正是 congruence / R-Comp。

**证明**:对 $E$ 结构归纳。各 case 用到的规则:

- **var $x$** — 用 $\sim_K$:$\kappa_{mc}(\rho_{mc}x)\gamma=\gamma(\kappa_c(\rho_c x))$。
- **$\lambda x.E$** — 先用 $\sim_P$(由 IH)造出相关过程,再用 $\sim_K$。
- **$E_1E_2$** — 内层 continuation $\lambda a\gamma_2.f\,a\,\kappa\,\gamma_2$ 关系性 **唯一**用到 $\sim_P$
  (R-Proc):因为 $f$ 是从子表达式流出的、对外不透明的过程,只能整体打包。
- **if** — 用 IH + if-distrib($\gamma$ 是全函数,与 meta-`if` 交换)。
- **shift $\xi k.E$** — 需 $\iota_{mc}\sim_K\iota_c$(**这里用到 $\gamma$ 尊重 $\sim_V$**)与
  reified 过程 $\sim_P$;注意 $\kappa_{mc}$ 落在 $\gamma$ **外面**(被捕获的 delimited continuation)。
- **reset $\langle E\rangle$** — 用 $\sim_K$ 造新 MCont $\widehat\gamma=\lambda v.\kappa_{mc}v\gamma$。

取 $\kappa=\iota$、$\gamma=\mathrm{id}$ 得顶层正确性
$\mathcal{E}_{mc}[\![E]\!]\rho\,\iota_{mc}\,\mathrm{id}=\mathcal{E}_c[\![E]\!]\rho\,\iota_c$。$\blacksquare$

**尊重性封闭引理**:$\mathrm{id}$、reset 造的 $\lambda v.\kappa v\gamma$、shift 造的 $\lambda w.\kappa' w\gamma'$
都尊重 $\sim_V$(由 $\sim_K$ + 已有尊重性逐一验证),故证明中每处 $\gamma$ 都合法。

---

## 4. 抽象机(defunctionalize MCS)

把 $\mathrm{Cont}_{mc}$ 与 $\mathrm{MCont}$ 两层函数空间一阶化:

- $\mathrm{Cont}_{mc}$ → 数据类型 `K`(控制栈 / 当前 delimited continuation);
- $\mathrm{MCont}$ → 数据类型 `C`(元控制栈 / 定界符链)。

得到 `applyK :: K -> Value -> C -> Value`、`applyC :: C -> Value -> Value`、
`eval :: Env -> Expr -> K -> C -> Value`(= 一阶化的 `evalMK`)。关键转移:

```
eval env (EShift x body) k c = eval (insert x (VCont k) env) body KEmpty c   -- 捕获 k 为值,重置续延
eval env (EReset body)   k c = eval env body KEmpty (CReset k c)             -- 压入定界符
applyProc (VCont k0) v k c    = applyK k0 v (CShift k c)                      -- 恢复被捕获的续延
```

这正是 shift/reset 的两层栈抽象机(CK + meta-stack)。完整可运行代码见
[src/Shift/Machine/Eval.hs](../src/Shift/Machine/Eval.hs),其中
`example`($1 + \langle 10 + \xi k.\,100\rangle$)求值为 `VInt 101`。

**正确性(refunctionalization)**:对 `K`、`C` 各定义 refunctionalize 映射 $|\cdot|$,则
$\mathrm{applyK}\,k\,v\,c=|k|\,v\,|c|$、$\mathrm{applyC}\,c\,v=|c|\,v$、
$\mathrm{eval}\,\rho\,e\,k\,c=\mathrm{evalMK}\,\rho\,e\,|k|\,|c|$ —— 机器与 MCS 逐步对应。

---

## 5. 方法论:stepwise vs combined

- **stepwise**(论文说的 "standard CPS conversion"):把 CCS 方程当 definitional interpreter,
  机械套 Plotkin CPS。简单,因为**正确性是一次性元定理**(本文第 3 节基本引理)。
- **combined**(规范驱动 calculation,Bahr–Hutton 风格):从 congruence 出发逐 case 计算,
  把那条元定理**摊进每个 case**,于是 R-κ/R-Proc/R-Comp/if-distrib 一一现形。

二者**同一终点、两条路**;差距不是难易,而是论证粒度。详见
[Papers/References.md](References.md) §4 速查表。
