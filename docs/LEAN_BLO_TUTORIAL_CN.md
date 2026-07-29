# OUSVR-BLO Lean 形式化理解教程

## 目标读者

本文面向已经了解双层优化（BLO）、在线 value anchor、LLM/LoRA 优化应用背景，但只具备基础数学证明阅读经验的读者。

目标不是学习 Lean 语法，而是理解：

1. 论文中的证明结构如何映射到 Lean；
2. 为什么需要 Lyapunov 势函数；
3. 一个单步下降不等式如何变成有限时间收敛界；
4. 当前形式化证明覆盖什么，没有覆盖什么。

---

# 1. 项目定位

本项目形式化的是修订版 OUSVR-BLO online value-anchor theorem 的证明骨架。

Lean 验证的核心包括：

- one-step Lyapunov descent；
- finite-horizon budget summation；
- averaged stationarity bound；
- averaged residual bound；
- enhanced improvement theorem；
- proxy calibration certificate。

项目不是证明真实 LLM/LoRA 系统一定满足所有数学假设，而是在明确接口假设下验证证明链条。

---

# 2. 阅读路线

推荐顺序：

```
ProxyCertificate
        ↓
ScalarFacts
        ↓
SafetyDescent
        ↓
LyapunovBudget
        ↓
ImprovementDescent
        ↓
AnalyticInterfaces
        ↓
LocalSurrogate
```

不要从 Lean 文件顶部开始阅读。数学结构比代码顺序更重要。

---

# 3. 核心思想：势函数预算

BLO 中存在两个目标：

- 外层优化目标下降；
- value anchor 残差保持稳定。

单独分析外层目标：

$$
P_{t+1}\le P_t-\eta G_t^2+error
$$

通常不足够，因为 anchor 误差会反过来影响梯度。

因此构造：

$$
\Psi_t=P_t+\alpha R_t
$$

其中：

- $P_t$ 是外层目标；
- $R_t$ 是 anchor residual；
- $\alpha$ 是平衡系数。

目标变成证明：

$$
\Psi_{t+1}\le \Psi_t-有效下降+误差项
$$

---

# 4. 三个基本接口

## 4.1 外层下降

假设：

$$
P_{t+1}\le P_t-\frac\eta2G_t^2
+\frac{\eta\lambda^2}{2}(C_R\hat R_t+b_t)
$$

含义：

- $G_t^2$ 提供优化进展；
- anchor 误差产生额外代价。

---

## 4.2 residual 漂移

假设：

$$
R_{t+1}\le(1+C_R\beta)\hat R_t
+2A_\eta G_t^2+\beta b_t+d_t
$$

含义：

即使修正了 anchor，外层变量变化仍会导致 residual 增长。

---

## 4.3 safeguard 收缩

假设：

$$
\hat R_t\le(1-\theta)R_t+\epsilon_t
$$

表示在线 anchor 更新具有收缩能力。

---

# 5. 一步 Lyapunov 证明

将 residual 漂移乘以 $\alpha$：

$$
\alpha R_{t+1}
$$

然后和 $P_{t+1}$ 相加：

$$
P_{t+1}+\alpha R_{t+1}
$$

得到：

$$
\Psi_{t+1}
\le
\Psi_t
-\frac\eta4G_t^2
-\frac{\eta\lambda^2C_R}{4}R_t
+C_\epsilon\epsilon_t
+C_bb_t
+C_dd_t
$$

关键点：

1. 选择合适 $\alpha$ 抵消 residual 增长；
2. 步长限制保证 $G_t^2$ 前仍然为负；
3. 剩余部分进入误差预算。

---

# 6. 从一步下降到有限时间界

对：

$$
\Psi_{t+1}-\Psi_t
$$

从 $0$ 到 $T-1$ 求和。

左侧望远镜：

$$
\sum(\Psi_{t+1}-\Psi_t)=\Psi_T-\Psi_0
$$

得到：

$$
\frac\eta4\sum G_t^2
+rac{\eta\lambda^2C_R}{4}\sum R_t
\le
\Psi_0-P_\star
+误差预算
$$

这就是 Lean 中的 cumulative budget。

---

# 7. 平均驻点界

因为：

$$
R_t\ge0
$$

可以删除 residual 项：

$$
\frac\eta4\sum G_t^2\le预算
$$

除以 $T$：

$$
\frac1T\sum G_t^2\le O(1/T)+平均误差
$$

这对应 `gradient_average_bound`。

---

# 8. 增强版 improvement theorem

增强版增加：

$$
\Delta_t\ge0
$$

表示 online anchor 相比 baseline 的改进。

下降式增加：

$$
-\frac{\eta\lambda^2}{2}\Delta_t
$$

因此最终可以同时控制：

$$
\frac1T\sum G_t^2
+
2\lambda^2\frac1T\sum\Delta_t
$$

---

# 9. Proxy certificate

proxy 误差满足：

$$
|\hat e_O-e_O|\le\rho
$$

$$
|\hat e_B-e_B|\le\rho
$$

如果 proxy 判断：

$$
\hat e_O\le\hat e_B-\Delta
$$

则：

$$
e_O\le e_B-\Delta+2\rho
$$

这是整个项目中最简单、最适合学习 Lean 的证明。

---

# 10. Lean 阅读方法

看到：

```lean
structure X where
```

理解为：

> 定义一个数学对象，并列出所有假设。

看到：

```lean
theorem A : B := by
```

理解为：

> 在已有假设下证明结论 B。

常见 tactic：

- `have`：建立中间公式；
- `linarith`：线性不等式组合；
- `nlinarith`：非线性多项式不等式；
- `ring_nf`：展开整理代数式。

Lean 不负责创造证明思路，只检查每一步是否合法。

---

# 11. 当前证明边界

已验证：

- Lyapunov 系数计算；
- 有限时间求和；
- 平均界推导；
- proxy certificate。

尚未验证：

- 真实神经网络一定满足所有 smoothness 假设；
- online anchor 一定存在且唯一；
- 完整非凸 BLO 全局收敛；
- LLM/LoRA 实际训练自动满足接口。

因此当前结果应理解为：

> 在明确数学接口成立时，OUSVR-BLO 证明链经过机器检查。

而不是：

> 任意真实训练过程必然收敛。

---

# 12. 推荐进一步扩展

后续可以增加：

1. 每个 theorem 对应的数学图谱；
2. BLO 算法变量到 Lean 变量的映射表；
3. 每个不等式步骤的人工推导；
4. Lean proof 与论文公式编号对应表。
