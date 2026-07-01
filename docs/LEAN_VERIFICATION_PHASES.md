# Lean 形式验证阶段说明

本文档说明当前仓库对附件证明的 Lean 覆盖范围、每个阶段回答的问题，以及仍保留为接口假设的内容。

## 阶段一：核心定理验证

目标是验证主定理中最容易发生系数错误的代数链条：

- one-step Lyapunov descent；
- finite-horizon telescoping budget；
- averaged gradient stationarity bound；
- averaged residual bound。

该阶段回答的问题是：在 residual contraction、residual-to-gradient control、residual drift 等接口假设成立时，主定理的下降预算和平均收敛界是否正确。

对应 Lean 文件：

- `OUSVRBLO/ScalarFacts.lean`
- `OUSVRBLO/LyapunovBudget.lean`
- `OUSVRBLO/SafetyDescent.lean`

## 阶段二：整体验证

目标是覆盖附件从 safety theorem 到 enhanced theorem，再到 proxy certificate 的完整证明链条：

- upper-gradient improvement 进入 Lyapunov 预算；
- 修订后的 `Czeta` 系数；
- `zeta_t` 同时进入 descent 与 residual drift；
- proxy calibration 推出 true error improvement；
- enhanced `R2+` 接口闭合。

该阶段回答的问题是：附件修订版的整体 proof claim 在 interface theorem 层面是否闭合。

对应 Lean 文件：

- `OUSVRBLO/ImprovementDescent.lean`
- `OUSVRBLO/ProxyCertificate.lean`

## 阶段三：完整细致验证

目标是开始把部分外部 hypotheses 替换为 Lean 中的充分条件定理和抽象接口：

- scalar smooth descent lemma；
- residual-to-gradient error bound 的 Lipschitz/error-bound 推导；
- local regularized lower surrogate；
- value-response interface。

该阶段回答的问题是：哪些“假设合理性”可以继续下沉为机器检查的数学充分条件。

对应 Lean 文件：

- `OUSVRBLO/AnalyticInterfaces.lean`
- `OUSVRBLO/LocalSurrogate.lean`

## 不证明的内容

当前仓库不证明：

- 真实 LLM/LoRA 微调过程自动满足全部 analytic hypotheses；
- general nonconvex BLO global convergence；
- original BLO KKT convergence；
- 具体 safeguard 程序的可执行正确性。

这些内容需要额外的模型、算法和分析假设。当前 Lean 结果的意义是：在明确列出的接口假设下，附件证明的核心代数结构、增强证明链条和若干分析接口充分条件已经由 Lean 检查。

## 验收命令

```powershell
C:\Users\lx\.elan\bin\lake.exe build
& 'C:\Program Files\Git\bin\bash.exe' scripts/check_no_placeholder.sh
```
