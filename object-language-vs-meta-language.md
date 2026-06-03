# 对象语言和元语言的区分

在讨论 `evalK`、CPS conversion 和 meta-continuation semantics 时，一个很容易混淆的点是：

- 什么属于对象语言；
- 什么属于元语言；
- 哪些 application 应该当成普通 CPS application 来转换；
- 哪些 application 可以当成 trivial / atomic operation。

这份笔记整理这个区分。

## 1. 对象语言是什么？

对象语言是我们正在研究、解释、定义语义的那门语言。

在当前例子里，对象语言大概可以写成：

```haskell
data Expr
  = Var Name
  | Lam Name Expr
  | App Expr Expr
  | Reset Expr
  | Shift Name Expr
  | CallCC Name Expr
```

也就是说，对象语言里的构造包括：

```haskell
Var x
Lam x body
App e1 e2
Reset body
Shift c body
CallCC c body
```

因此，对象语言里的函数调用是这个语法构造：

```haskell
App e1 e2
```

例如，对象语言程序：

```haskell
(\x -> x) 10
```

在语法树中可以表示成：

```haskell
App (Lam x (Var x)) 10
```

这里的 `App` 是对象语言中的 application syntax。

## 2. 元语言是什么？

元语言是我们用来描述对象语言语义的语言。

在这里，元语言就是 Haskell 或 pseudo-Haskell。

例如下面这些都是元语言里的函数调用：

```haskell
evalK env e k
env x
k v
f a k
```

它们不是对象语言的语法节点，而是解释器自身在运行时执行的操作。

所以要区分：

```haskell
App e1 e2
```

这是对象语言里的 application syntax。

而：

```haskell
evalK env e k
env x
k v
f a k
```

这些都是元语言里的 application expression。

## 3. 对象语言函数值如何表示？

一个容易混淆的地方是：对象语言里的函数值通常会被解释成元语言函数。

例如：

```haskell
evalK env (Lam x body) k =
  k (\v k' -> evalK (env[x -> v]) body k')
```

对象语言里的 lambda：

```haskell
Lam x body
```

被解释成了一个元语言函数：

```haskell
\v k' -> evalK (env[x -> v]) body k'
```

因此，在 `App` case 里：

```haskell
evalK env (App e1 e2) k =
  evalK env e1 (\f -> evalK env e2 (\a -> f a k))
```

这里的：

```haskell
f a k
```

表面上是元语言函数调用。

但是它调用的 `f` 是对象语言函数值的语义表示。

所以：

```haskell
App e1 e2
```

是对象语言里的函数调用语法。

而：

```haskell
f a k
```

是解释器用来执行这个对象语言函数调用的元语言函数调用。

换句话说，`f a k` 是对象语言 application 和元语言 application 的连接点。

## 4. 几类 application 的分类

下面按照是否需要当成非平凡计算处理来分类。

### 4.1 `env x`

```haskell
env x
```

这是元语言里的环境查询。

它只是查找变量 `x` 在环境 `env` 中绑定到什么值。

它不代表对象语言中的函数调用，也不携带控制效果，不会捕获、调用或组合 continuation。

因此在这份推导里，通常把它当成 trivial / atomic term：

```haskell
[[ env x ]] = env x
```

也就是说，不对它使用普通的 CPS application rule。

### 4.2 `evalK env e k`

```haskell
evalK env e k
```

这是元语言里的递归语义调用。

它表示继续解释对象语言表达式 `e`。

由于 `e` 里面可能出现：

```haskell
Shift c body
Reset body
CallCC c body
App e1 e2
```

所以 `evalK env e k` 不能当成 trivial operation。

在 meta-CPS 转换之后，它会变成：

```haskell
evalMK env e [[ k ]] mk
```

如果 `k` 本身是 lambda，则这个 lambda 也需要继续 CPS-transform。

### 4.3 `k v`

```haskell
k v
```

这是元语言里的 continuation application。

它不是对象语言里的函数调用语法，但它直接表示控制流的继续执行。

在 meta-CPS 转换之后：

```haskell
[[ k v ]]
=> \mk -> k v mk
```

这里 `mk` 是 meta-continuation。

### 4.4 `k' (k v)`

```haskell
k' (k v)
```

这里外层和内层都是 continuation application。

因为参数 `k v` 本身是非平凡计算，所以必须先执行 `k v`，再把结果传给 `k'`：

```haskell
[[ k' (k v) ]]
=> \mk -> k v (\x -> k' x mk)
```

这正是 `Shift` case 中出现 continuation composition 的原因。

### 4.5 `f a k`

```haskell
f a k
```

这是元语言里的函数调用。

不过 `f` 是对象语言函数值的语义表示。

因此 `f a k` 是解释器用来执行对象语言 application 的元语言调用。

在 meta-CPS 转换之后：

```haskell
[[ f a k ]]
=> \mk -> f a k mk
```

所以它也使用了 CPS application rule。

它看起来只是多传了一个 `mk`，是因为 `f`、`a`、`k` 在这里都已经是值。

## 5. 更准确的说法

原先的说法：

> 只有 continuation 作为 application 的 function 时，才需要使用 CPS conversion 中的 application rule。

这个说法不够准确。

更准确的说法是：

> 标准 CPS conversion 的 application rule 原则上作用于所有非平凡 application。  
> 但是在这份推导里，`env x` 这类纯的元语言环境查询被当成 atomic term；`evalK env e k` 被识别为递归语义调用并翻译成 `evalMK env e [[k]] mk`；`f a k` 被解释为调用已经 CPS 化后的对象语言函数值。  
> 因此，continuation application 如 `k v` 和 `k' (k v)` 是最关键、最不应该被简化掉的 application，因为它们显式决定了 meta-continuation 如何传递和组合。

一句话总结：

> 不是只有 continuation application 才使用 CPS application rule；而是 continuation application 是最关键、最体现控制流结构的 application。`env x` 则因为是纯的元语言环境查询，可以被当成 trivial / atomic term。

## 6. 最简界定标准

可以用下面的标准来区分对象语言和元语言。

如果它是被解释语言的语法构造，例如：

```haskell
Var x
Lam x body
App e1 e2
Reset body
Shift c body
CallCC c body
```

那么它属于对象语言。

如果它是解释器代码中用来定义语义的函数、环境、continuation 或递归调用，例如：

```haskell
evalK env e k
env x
k v
f a k
```

那么它属于元语言。

其中 `f a k` 是一个桥接点：

```haskell
App e1 e2
```

是对象语言的 application syntax。

```haskell
f a k
```

是元语言中执行这个对象语言 application 的语义操作。
