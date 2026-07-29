# OUSVR-BLO Lean 项目协作者理解指南

## 目标

本指南面向主要负责实验、模型训练和结果分析，但不负责形式化证明的论文合作者。

目标不是让协作者学习 Lean，而是让其能够回答：

1. 实验验证的是哪个理论结论；
2. 理论假设对应实验中的哪些可观测量；
3. 修改算法或实验设置时，哪些理论部分可能失效；
4. 论文中的 theorem、experiment、figure 如何保持一致。

## 推荐阅读路径

```text
实验问题
  |
  v
BLO算法机制
  |
  v
理论对象映射表
  |
  v
接口假设
  |
  v
Lean证明结构
  |
  v
实验验证指标
```

## 第一层：从实验理解理论

实验人员首先不阅读 Lean 文件，而阅读：

- 方法解决什么 BLO 问题；
- value-anchor 为什么需要稳定性保证；
- online anchor improvement 为什么有意义；
- 哪些量能够通过训练日志估计。

核心对象：

|数学对象|实验解释|
|-|-|
|$G_t^2$|外层优化残差或梯度驻点指标|
|$R_t$|value anchor 残差|
|$\Delta_t$|online anchor 相对 baseline 的改进|
|$\epsilon_t$|safeguard误差|
|$b_t$|梯度近似误差|
|$d_t$|动态漂移误差|
|$\zeta_t$|proxy校准误差|

## 第二层：理解论文证明结构

论文证明不是直接证明“LLM训练一定收敛”。

当前 Lean 验证的是接口定理：

如果以下条件成立：

- 外层下降关系；
- residual drift 控制；
- safeguard contraction；
- proxy calibration；

那么可以推出：

- 有限时间 Lyapunov budget；
- 平均驻点界；
- 平均 residual 界；
- enhanced improvement bound。

## 第三层：实验和理论对齐检查表

新增实验时必须回答：

### 算法一致性

- 实验代码中的 anchor 更新是否对应理论中的 $\widehat R_t$？
- 是否引入新的误差项？
- 是否改变 safeguard 规则？

### 参数一致性

- 学习率是否满足理论中的步长限制？
- contraction factor 是否可以估计？
- proxy error 是否有独立测量方法？

### 图表一致性

每个实验图应注明对应理论量：

|图|理论对应|
|-|-|
|训练曲线|$P_t$ 或 Lyapunov变化|
|anchor误差曲线|$R_t$|
|baseline比较|$\Delta_t$|
|proxy误差分析|$\zeta_t$|

## 第四层：Lean文件导航

```text
ProxyCertificate.lean
    ↓
最简单的不等式链

SafetyDescent.lean
    ↓
一步Lyapunov下降

LyapunovBudget.lean
    ↓
有限时间求和

ImprovementDescent.lean
    ↓
增强版online anchor改进

AnalyticInterfaces.lean
    ↓
部分假设的进一步数学展开
```

## 第五层：论文修改流程

任何理论修改采用：

1. 修改论文公式；
2. 更新符号映射表；
3. 更新 Lean interface；
4. 检查 theorem 是否仍成立；
5. 更新实验验证项。

禁止出现：

- 论文使用的符号和 Lean 不一致；
- 实验实现已经改变但理论仍描述旧算法；
- theorem 宣称超出 Lean 验证范围。

## 当前明确边界

已验证：

- Lyapunov 系数计算；
- 有限时间预算求和；
- 平均界推导；
- proxy certificate 代数关系。

未验证：

- 真实 LLM/LoRA 系统自动满足所有分析假设；
- 一般非凸 BLO 全局收敛；
- 具体训练程序实现正确性。

## 最终目标

该仓库应成为论文共同维护的单一理论来源：

实验人员通过本指南理解理论约束，理论人员通过 Lean 保证公式链正确，论文中的定理、实验和代码保持同步。
