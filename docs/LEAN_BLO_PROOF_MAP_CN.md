# OUSVR-BLO Proof Map（论文协作者版）

## 目标

本文档用于帮助主要负责实验、代码和论文整合的合作者理解 Lean 形式化部分。

阅读目标不是学习 Lean 语法，而是回答：

- 实验中的哪个机制对应哪个数学对象；
- 论文中的哪个公式已经被 Lean 验证；
- 修改算法或实验时需要同步修改哪些理论接口；
- 当前证明覆盖什么，没有覆盖什么。

---

# 1. 总体证明结构

```text
BLO 在线 value-anchor 方法
          |
          v
数学模型与误差分解
          |
          v
接口假设
(residual contraction / drift / gradient error)
          |
          v
SafetyStepSystem
          |
          v
Lyapunov 势函数
Psi_t = P_t + alpha R_t
          |
          v
one-step Lyapunov descent
          |
          v
finite-horizon budget
          |
    +-----+------+
    |            |
    v            v
stationarity   residual
bound          bound

          |
          v
ImprovementStepSystem
          |
          v
Delta improvement + proxy certificate
          |
          v
Enhanced theorem
```

---

# 2. 核心对象映射

|数学对象|Lean对象|实验含义|
|-|-|-|
|$P_t$|`P`|外层目标函数或价值误差|
|$R_t$|`R`|value-anchor残差|
|$\hat R_t$|`Rhat`|经过 safeguard 后的残差|
|$G_t^2$|`Gsq`|外层驻点性指标|
|$\Delta_t$|`Delta`|online anchor 相比 baseline 的改进|
|$\epsilon_t$|`eps`|残差收缩误差|
|$b_t$|`b`|梯度/value近似误差|
|$d_t$|`d`|残差漂移误差|
|$\zeta_t$|`zeta`|proxy校准误差|

---

# 3. Safety theorem 路径

## 输入接口

实验或算法分析需要提供三个关系：

## 3.1 外层下降

```text
P(t+1) <= P(t)
          - eta/2 * Gsq(t)
          + eta*lambda^2/2*(CR*Rhat(t)+b(t))
```

对应：

`SafetyStepSystem.descent`

---

## 3.2 residual 漂移

```text
R(t+1) <= (1+CR*beta)Rhat(t)
          + 2*Aeta*Gsq(t)
          + beta*b(t)
          + d(t)
```

对应：

`SafetyStepSystem.drift`

---

## 3.3 safeguard 收缩

```text
Rhat(t) <= (1-theta)R(t)+eps(t)
```

对应：

`SafetyStepSystem.contraction`

---

# 4. Lyapunov 证明

构造：

```text
Psi(t)=P(t)+alpha*R(t)
```

其中：

```text
alpha = eta*lambda^2*CR/theta
```

目的：

让 residual 增长项被 contraction 抵消。

最终得到：

```text
Psi(t+1)<=Psi(t)
 - eta/4*Gsq(t)
 - eta*lambda^2*CR/4*R(t)
 + error terms
```

对应：

`SafetyStepSystem.one_step_lyapunov`

---

# 5. 从单步到有限时间界

单步下降累加：

```text
sum(Psi(t+1)-Psi(t))
```

产生望远镜求和：

```text
Psi(T)-Psi(0)
```

得到 budget：

```text
progress <= initial energy + accumulated errors
```

对应：

`SafetyStepSystem.cumulative_budget`

---

# 6. 实验指标对应

从 budget 中丢弃非负项：

## 平均驻点界

关注：

```text
1/T * sum Gsq(t)
```

实验对应：

- gradient norm；
- stationarity metric；
- validation objective improvement。

---

## 平均残差界

关注：

```text
1/T * sum R(t)
```

实验对应：

- anchor approximation error；
- lower response mismatch。

---

# 7. Enhanced theorem

增强版增加：

```text
Delta(t) >= 0
```

表示 online anchor 的额外收益。

下降式增加：

```text
-eta*lambda^2/2*Delta(t)
```

同时引入：

```text
zeta(t)
```

表示 proxy 与真实误差之间的不一致。

对应：

`ImprovementStepSystem`

---

# 8. Proxy certificate

实验中通常无法直接比较真实误差，因此使用 proxy：

```text
|proxyO-trueO| <= rho
|proxyB-trueB| <= rho
```

若：

```text
proxyO <= proxyB-DeltaHat
```

则：

```text
trueO <= trueB-DeltaHat+2rho
```

对应：

`ProxyComparison.true_error_improves`

---

# 9. 修改实验时的同步检查

## 修改训练算法

检查：

1. descent 是否仍成立；
2. residual drift 是否变化；
3. 是否增加新的 error term。

---

## 修改 anchor 方法

检查：

1. 是否改变 Delta 定义；
2. 是否改变 proxy certificate；
3. 是否需要重新定义 zeta。

---

## 修改实验指标

检查：

1. 指标是否对应 theorem 中变量；
2. 是否只能说明经验现象，不能扩大 theorem claim。

---

# 10. 当前证明边界

## Lean 已验证

- Lyapunov 系数计算；
- 单步下降组合；
- 有限时间预算；
- 平均驻点界；
- 平均 residual 界；
- proxy algebra。

## 未验证

- LLM/LoRA训练一定满足所有假设；
- 一般非凸 BLO 全局收敛；
- 实际 safeguard 程序实现正确；
- 原始 BLO KKT 收敛。

因此论文表述应保持：

> 在给定 analytic interface assumptions 下，OUSVR-BLO proof skeleton 和有限时间保证被机器检查。
