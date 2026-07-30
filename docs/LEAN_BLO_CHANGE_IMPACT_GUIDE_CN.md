# OUSVR-BLO 修改影响分析指南

## 目的

本文用于实验协作者和论文维护者判断：当算法、实现、实验指标或论文描述发生变化时，哪些理论接口、Lean 文件和实验结果需要同步更新。

目标不是要求所有协作者掌握 Lean，而是建立：

```
实验修改
   ↓
理论对象变化
   ↓
Lean 接口影响
   ↓
论文表述影响
```

的快速判断流程。

---

## 1. 修改算法结构

### 1.1 修改 value anchor 更新策略

可能影响：

- anchor residual 定义；
- residual contraction 假设；
- proxy comparison；
- improvement certificate。

需要检查：

```
ImprovementStepSystem
        |
        +-- Delta
        +-- zeta
        +-- improved_descent
        +-- improved_drift
```

核心问题：

> 新的 anchor 方法是否仍能提供可证明的 residual reduction？

---

## 2. 修改 safeguard 机制

影响路径：

```
safeguard
    ↓
Rhat contraction
    ↓
alpha choice
    ↓
Lyapunov descent
```

重点检查：

- contraction 系数 theta 是否变化；
- residual drop coefficient 是否仍为正；
- alpha 是否需要重新设计。

相关 Lean：

- SafetyStepSystem.contraction
- SafetyStepSystem.one_step_lyapunov

---

## 3. 修改优化器或 outer update

影响：

```
outer optimizer
       ↓
P descent
       ↓
Gsq coefficient
```

需要重新确认：

- smooth descent 是否成立；
- step size 条件是否满足；
- Gsq 是否仍表示相同驻点指标。

相关文件：

- AnalyticInterfaces.lean
- SafetyDescent.lean

---

## 4. 修改 loss 或模型结构

需要区分两类：

### 仅改变实验对象

例如：

- 不同数据集；
- 不同 LoRA rank；
- 不同训练轮数。

通常不影响 Lean。

需要更新：

- 实验配置；
- 指标统计。

### 改变理论对象

例如：

- value function 定义变化；
- surrogate objective 变化；
- residual 定义变化。

需要检查：

- LocalSurrogate
- ValueFunctionInterface
- ResidualGradientInterface

---

## 5. 新增实验指标

新增指标必须回答：

该指标对应哪个理论量？

映射关系：

|理论量|实验含义|
|-|-|
|Gsq|外层优化驻点程度|
|R|anchor residual|
|Delta|online anchor 改进|
|zeta|proxy 校准误差|

如果无法建立映射，则该实验只能作为经验结果，不能作为 theorem 支撑。

---

## 6. 修改论文公式

论文公式修改流程：

```
论文公式
   ↓
符号表更新
   ↓
Lean structure 更新
   ↓
定理重新验证
   ↓
实验解释同步
```

禁止：

- 论文中增加未被 Lean 检查的系数；
- 实验中使用新算法但 theorem 仍描述旧算法；
- 将 interface theorem 描述成完整 convergence theorem。

---

## 7. 版本同步检查表

提交实验变化时：

- [ ] 算法描述是否变化
- [ ] 理论假设是否变化
- [ ] Lean interface 是否需要修改
- [ ] theorem 是否仍覆盖该算法
- [ ] 实验指标是否对应理论量
- [ ] limitation 描述是否需要更新

---

## 8. 当前项目边界

当前 Lean 验证重点：

- Lyapunov coefficient accounting；
- finite horizon budget；
- averaged bounds；
- proxy certificate。

当前没有验证：

- 真实 LLM/LoRA 系统一定满足全部 analytic hypotheses；
- 一般非凸 BLO 全局收敛；
- 工程实现完全正确。

因此任何论文修改都需要保持：

> Lean 验证范围 = 论文理论承诺范围。
