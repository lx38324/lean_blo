# OUSVR-BLO Lean 形式验证 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 分阶段完成附件证明的 Lean 形式验证，使用户无需人工逐行核对全部推导，也能理解证明骨架并确认理论结论在明确假设下成立。

**Architecture:** 采用三层验证路线：先验证核心定理的 Lyapunov 预算与平均收敛结论，再验证附件整体证明链条中的增强定理和 proxy certificate，最后在需要时进一步形式化 smoothness、value-gradient interface、residual drift 等分析假设的充分条件。Lean 文件按证明责任拆分，避免把所有内容塞进 `LyapunovBudget.lean`。

**Tech Stack:** Lean 4, Mathlib, Lake, GitHub Actions, Windows PowerShell, Bash placeholder checker.

---

## 总体策略

本计划把“完整 Lean 形式验证”拆成三个可交付阶段：

1. **阶段一：核心定理验证**
   - 目标：验证附件主定理中真正容易出错的代数部分。
   - 覆盖：one-step Lyapunov descent、finite-horizon summation、averaged gradient stationarity bound、averaged residual bound。
   - 假设边界：smoothness、residual contraction、residual-to-gradient control、residual drift 作为显式 hypotheses。
   - 交付价值：确认主定理的下降预算和最终收敛界没有系数错误。

2. **阶段二：整体验证**
   - 目标：覆盖附件从 safety theorem 到 enhanced theorem 再到 proxy certificate 的完整证明链条。
   - 覆盖：upper-gradient improvement、修订后的 `C_zeta`、`zeta_t` 进入 residual drift、proxy calibration 推出 `R2+`。
   - 假设边界：仍不声称证明 LLM 微调场景自动满足这些假设。
   - 交付价值：确认附件整体 claim 在 interface theorem 层面闭合。

3. **阶段三：完整细致验证**
   - 目标：逐步把若干外部 hypotheses 替换为 Lean 中的充分条件定理。
   - 覆盖：smooth descent lemma、residual-to-gradient error bound 的 Lipschitz/error-bound 推导、residual drift 的 Lipschitz 型充分条件、局部正则化 lower surrogate 的抽象定义。
   - 假设边界：不会证明真实神经网络训练全局非凸性质，也不会证明 original BLO KKT convergence。
   - 交付价值：把“假设合理性”也纳入 Lean 检查的一部分，但这是更长线的数学工程。

推荐执行顺序是阶段一和阶段二先闭合；如果目标是节省人工验证精力，阶段二完成后就已经能给出很强的结构性确认。阶段三适合作为后续增强，不应阻塞前两阶段。

## 当前仓库状态

当前仓库已有：

- `OUSVRBLO/LyapunovBudget.lean`
  - 已验证从 cumulative budget 推出 averaged stationarity/residual bounds。
  - 已包含 safety budget 和 improvement budget 两个结构。
- `OUSVRBLO.lean`
  - 当前只导入 `OUSVRBLO.LyapunovBudget`。
- `README.md` 与 `docs/FORMALIZATION_SCOPE.md`
  - 当前明确说明只覆盖 finite-horizon Lyapunov budget skeleton。
- `scripts/check_no_placeholder.sh`
  - 用于拒绝 Lean 源码中的占位证明关键词。

当前缺口：

- 没有形式化附件第 6 节从 one-step descent 到 cumulative budget 的推导。
- 没有形式化附件第 9 节增强版中 `zeta_t` 同时进入 descent 和 residual drift 的修订。
- 没有形式化附件第 10 节 proxy calibration certificate。
- 没有把附件各节映射到 Lean 文件的覆盖矩阵。

---

## 文件结构设计

新增或修改的文件按阶段分配：

- 修改：`lean-toolchain`
  - 用于固定 Lean 工具链，避免 `stable` 漂移造成 CI 与本地行为不同。
- 创建：`lake-manifest.json`
  - 用于锁定 Mathlib 依赖版本。
- 创建：`OUSVRBLO/ScalarFacts.lean`
  - 存放复用的实数不等式、有限和非负性、缩放恒等式。
- 创建：`OUSVRBLO/SafetyDescent.lean`
  - 阶段一核心文件。形式化主定理 one-step Lyapunov descent、求和和到 `SafetyBudget` 的连接。
- 创建：`OUSVRBLO/ImprovementDescent.lean`
  - 阶段二核心文件。形式化增强版 theorem，尤其是 corrected `C_zeta`。
- 创建：`OUSVRBLO/ProxyCertificate.lean`
  - 阶段二辅助文件。形式化 proxy calibration 推出 true error improvement。
- 创建：`OUSVRBLO/AnalyticInterfaces.lean`
  - 阶段三入口文件。形式化 smoothness、inexact update、gradient error、drift compatibility 的抽象接口。
- 创建：`OUSVRBLO/LocalSurrogate.lean`
  - 阶段三扩展文件。记录局部正则化 lower surrogate 和 value function 的抽象定义。
- 修改：`OUSVRBLO/LyapunovBudget.lean`
  - 尽量只保留现有 finite-horizon budget 结果；必要时补充命名 theorem，不做大重构。
- 修改：`OUSVRBLO.lean`
  - 统一导入新增 Lean 模块。
- 修改：`README.md`
  - 更新当前覆盖范围、构建方式、假设边界。
- 修改：`docs/FORMALIZATION_SCOPE.md`
  - 改成 manuscript-to-Lean 覆盖矩阵。
- 创建：`docs/LEAN_VERIFICATION_PHASES.md`
  - 给用户读的中文阶段说明和验收标准。

---

## 阶段零：工具链与基线

### Task 0.1：安装并锁定 Lean 环境

**Files:**
- Modify: `lean-toolchain`
- Create: `lake-manifest.json`

- [ ] **Step 1：检查本地工具链**

Run:

```powershell
elan --version
lean --version
lake --version
```

Expected if installed:

```text
elan ...
Lean ...
Lake ...
```

Expected if missing:

```text
The term 'elan' is not recognized
```

- [ ] **Step 2：安装 Lean 工具链**

Run with network access:

```powershell
winget install --id Leanprover.Elan -e
```

Expected:

```text
Successfully installed
```

Close and reopen PowerShell, then run:

```powershell
elan --version
```

Expected:

```text
elan ...
```

- [ ] **Step 3：固定工具链**

If the current `lean-toolchain` still says `leanprover/lean4:stable`, replace it with a concrete Lean release after confirming compatibility with Mathlib.

Example target format:

```text
leanprover/lean4:v4.23.0
```

Run:

```powershell
lake update
```

Expected:

```text
lake-manifest.json is created or updated.
```

- [ ] **Step 4：验证当前仓库基线**

Run:

```powershell
lake exe cache get
lake build
bash scripts/check_no_placeholder.sh
```

Expected:

```text
Build completed successfully
```

The placeholder checker should exit with code 0.

- [ ] **Step 5：提交工具链基线**

Run:

```powershell
git status --short
git add lean-toolchain lake-manifest.json
git commit -m "chore: lock Lean build baseline"
```

Expected:

```text
[main ...] chore: lock Lean build baseline
```

If `lean-toolchain` does not change, only add `lake-manifest.json`.

---

## 阶段一：核心定理验证

阶段一的目标是验证主定理的核心：从 one-step Lyapunov 下降不等式推出 finite-horizon budget，再推出 averaged stationarity 和 residual bounds。这个阶段不处理 enhanced theorem 和 proxy certificate。

### Task 1.1：增加通用实数与有限和工具

**Files:**
- Create: `OUSVRBLO/ScalarFacts.lean`
- Modify: `OUSVRBLO.lean`

- [ ] **Step 1：创建 `ScalarFacts.lean`**

Create `OUSVRBLO/ScalarFacts.lean`:

```lean
import Mathlib

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

lemma sum_nonneg_range {T : ℕ} {a : ℕ → ℝ}
    (ha : ∀ t, 0 ≤ a t) :
    0 ≤ ∑ t in Finset.range T, a t := by
  exact Finset.sum_nonneg (fun t _ => ha t)

lemma drop_nonneg_add_right {a b c : ℝ}
    (h : a + b ≤ c) (hb : 0 ≤ b) :
    a ≤ c := by
  linarith

lemma scale_eta_quarter {eta T x : ℝ}
    (heta : eta ≠ 0) (hT : T ≠ 0) :
    (4 / (eta * T)) * ((eta / 4) * x) = (1 / T) * x := by
  field_simp [heta, hT]
  ring

lemma scale_eta_lam_CR_quarter {eta lam CR T x : ℝ}
    (hden : eta * lam ^ 2 * CR * T ≠ 0) :
    (4 / (eta * lam ^ 2 * CR * T)) *
      ((eta * lam ^ 2 * CR / 4) * x) = (1 / T) * x := by
  field_simp [hden]
  ring

end

end OUSVRBLO
```

- [ ] **Step 2：公开导入**

Modify `OUSVRBLO.lean`:

```lean
import OUSVRBLO.ScalarFacts
import OUSVRBLO.LyapunovBudget
```

- [ ] **Step 3：构建**

Run:

```powershell
lake build OUSVRBLO.ScalarFacts
```

Expected:

```text
Build completed successfully
```

- [ ] **Step 4：提交**

Run:

```powershell
git add OUSVRBLO/ScalarFacts.lean OUSVRBLO.lean
git commit -m "feat: add scalar proof helpers"
```

Expected:

```text
[main ...] feat: add scalar proof helpers
```

### Task 1.2：形式化主定理 one-step safety descent

**Files:**
- Create: `OUSVRBLO/SafetyDescent.lean`
- Modify: `OUSVRBLO.lean`

- [ ] **Step 1：创建 safety step system**

Create `OUSVRBLO/SafetyDescent.lean`:

```lean
import OUSVRBLO.LyapunovBudget
import OUSVRBLO.ScalarFacts

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

structure SafetyStepSystem where
  eta : ℝ
  lam : ℝ
  CR : ℝ
  theta : ℝ
  beta : ℝ
  Aeta : ℝ
  Pstar : ℝ
  P : ℕ → ℝ
  R : ℕ → ℝ
  Rhat : ℕ → ℝ
  Gsq : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  CR_pos : 0 < CR
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  Gsq_nonneg : ∀ t, 0 ≤ Gsq t
  R_nonneg : ∀ t, 0 ≤ R t
  P_lower : ∀ t, Pstar ≤ P t
  two_alpha_Aeta_le : 2 * (eta * lam ^ 2 * CR / theta) * Aeta ≤ eta / 4
  residual_drop_coeff :
    eta * lam ^ 2 * CR / theta
      - (1 - theta) *
        (eta * lam ^ 2 * CR / 2
          + (eta * lam ^ 2 * CR / theta) * (1 + CR * beta))
      ≥ eta * lam ^ 2 * CR / 4
  eps_coeff_bound :
    eta * lam ^ 2 * CR / 2
      + (eta * lam ^ 2 * CR / theta) * (1 + CR * beta)
      ≤ eta * lam ^ 2 * CR * (3 / 4 + 1 / theta)
  b_coeff_bound :
    eta * lam ^ 2 / 2 + (eta * lam ^ 2 * CR / theta) * beta
      ≤ 3 / 4 * eta * lam ^ 2
  descent :
    ∀ t,
      P (t + 1) ≤ P t
        - eta / 2 * Gsq t
        + eta * lam ^ 2 / 2 * (CR * Rhat t + b t)
  drift :
    ∀ t,
      R (t + 1) ≤
        (1 + CR * beta) * Rhat t
          + 2 * Aeta * Gsq t
          + beta * b t
          + d t
  contraction :
    ∀ t, Rhat t ≤ (1 - theta) * R t + eps t

def SafetyStepSystem.alpha (S : SafetyStepSystem) : ℝ :=
  S.eta * S.lam ^ 2 * S.CR / S.theta

def SafetyStepSystem.Psi (S : SafetyStepSystem) (t : ℕ) : ℝ :=
  S.P t + S.alpha * S.R t

def SafetyStepSystem.Ceps (S : SafetyStepSystem) : ℝ :=
  S.eta * S.lam ^ 2 * S.CR * (3 / 4 + 1 / S.theta)

def SafetyStepSystem.Cb (S : SafetyStepSystem) : ℝ :=
  3 / 4 * S.eta * S.lam ^ 2

def SafetyStepSystem.Cd (S : SafetyStepSystem) : ℝ :=
  S.alpha
```

Rationale: `beta` and `Aeta` are fields rather than definitions involving `Real.sqrt 2`. This keeps the first phase focused on the core theorem budget and avoids distracting square-root normalization work.

- [ ] **Step 2：证明 one-step Lyapunov descent**

Append:

```lean
theorem SafetyStepSystem.one_step_lyapunov
    (S : SafetyStepSystem) (t : ℕ) :
    S.Psi (t + 1) ≤ S.Psi t
      - S.eta / 4 * S.Gsq t
      - S.eta * S.lam ^ 2 * S.CR / 4 * S.R t
      + S.Ceps * S.eps t
      + S.Cb * S.b t
      + S.Cd * S.d t := by
  dsimp [SafetyStepSystem.Psi, SafetyStepSystem.alpha,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd]
  have hdes := S.descent t
  have hdrift := S.drift t
  have hcontr := S.contraction t
  nlinarith [hdes, hdrift, hcontr, S.two_alpha_Aeta_le,
    S.residual_drop_coeff, S.eps_coeff_bound, S.b_coeff_bound]
```

- [ ] **Step 3：证明 finite-horizon cumulative budget**

Append:

```lean
theorem SafetyStepSystem.cumulative_budget
    (S : SafetyStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Pstar
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d := by
  induction T with
  | zero =>
      simp [SeqSum]
      exact sub_nonneg.mpr (S.P_lower 0)
  | succ T ih =>
      rw [SeqSum, Finset.sum_range_succ, SeqSum, Finset.sum_range_succ,
        SeqSum, Finset.sum_range_succ, SeqSum, Finset.sum_range_succ,
        SeqSum, Finset.sum_range_succ]
      have hstep := S.one_step_lyapunov T
      nlinarith [ih, hstep]
```

- [ ] **Step 4：连接到现有 `SafetyBudget`**

Append:

```lean
def SafetyStepSystem.toBudget (S : SafetyStepSystem) (T : ℕ) :
    SafetyBudget T where
  eta := S.eta
  lam := S.lam
  CR := S.CR
  Psi0 := S.Psi 0
  Pstar := S.Pstar
  Ceps := S.Ceps
  Cb := S.Cb
  Cd := S.Cd
  Gsq := S.Gsq
  R := S.R
  eps := S.eps
  b := S.b
  d := S.d
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  CR_pos := S.CR_pos
  Gsq_nonneg := S.Gsq_nonneg
  R_nonneg := S.R_nonneg
  cumulative_budget := S.cumulative_budget T

theorem SafetyStepSystem.gradient_average_bound
    (S : SafetyStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ)) := by
  exact SafetyBudget.gradient_average_bound hT (S.toBudget T)

theorem SafetyStepSystem.residual_average_bound
    (S : SafetyStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  exact SafetyBudget.residual_average_bound hT (S.toBudget T)

end

end OUSVRBLO
```

- [ ] **Step 5：公开导入并构建**

Modify `OUSVRBLO.lean`:

```lean
import OUSVRBLO.ScalarFacts
import OUSVRBLO.LyapunovBudget
import OUSVRBLO.SafetyDescent
```

Run:

```powershell
lake build OUSVRBLO.SafetyDescent
lake build
```

Expected:

```text
Build completed successfully
```

- [ ] **Step 6：阶段一验收**

Run:

```powershell
bash scripts/check_no_placeholder.sh
```

Expected:

```text
exit code 0
```

Run:

```powershell
git add OUSVRBLO/ScalarFacts.lean OUSVRBLO/SafetyDescent.lean OUSVRBLO.lean
git commit -m "feat: verify core safety theorem"
```

Expected:

```text
[main ...] feat: verify core safety theorem
```

---

## 阶段二：整体验证

阶段二把附件增强版 theorem 和 proxy certificate 纳入 Lean，使整篇证明从 safety theorem 到 upper-gradient improvement 都闭合。

### Task 2.1：形式化 enhanced theorem 与 corrected `C_zeta`

**Files:**
- Create: `OUSVRBLO/ImprovementDescent.lean`
- Modify: `OUSVRBLO.lean`

- [ ] **Step 1：创建 improvement step system**

Create `OUSVRBLO/ImprovementDescent.lean`:

```lean
import OUSVRBLO.SafetyDescent

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

structure ImprovementStepSystem extends SafetyStepSystem where
  Delta : ℕ → ℝ
  zeta : ℕ → ℝ
  Delta_nonneg : ∀ t, 0 ≤ Delta t
  zeta_nonneg : ∀ t, 0 ≤ zeta t
  improved_descent :
    ∀ t,
      P (t + 1) ≤ P t
        - eta / 2 * Gsq t
        + eta * lam ^ 2 / 2 * (CR * Rhat t + b t)
        - eta * lam ^ 2 / 2 * Delta t
        + eta * lam ^ 2 / 2 * zeta t
  improved_drift :
    ∀ t,
      R (t + 1) ≤
        (1 + CR * beta) * Rhat t
          + 2 * Aeta * Gsq t
          + beta * b t
          + 2 * Aeta * lam ^ 2 * zeta t
          + d t

def ImprovementStepSystem.Czeta (S : ImprovementStepSystem) : ℝ :=
  S.eta * S.lam ^ 2 / 2 + 2 * S.alpha * S.Aeta * S.lam ^ 2
```

- [ ] **Step 2：证明 enhanced one-step Lyapunov descent**

Append:

```lean
theorem ImprovementStepSystem.one_step_lyapunov
    (S : ImprovementStepSystem) (t : ℕ) :
    S.Psi (t + 1) ≤ S.Psi t
      - S.eta / 4 * S.Gsq t
      - S.eta * S.lam ^ 2 * S.CR / 4 * S.R t
      - S.eta * S.lam ^ 2 / 2 * S.Delta t
      + S.Ceps * S.eps t
      + S.Cb * S.b t
      + S.Cd * S.d t
      + S.Czeta * S.zeta t := by
  dsimp [SafetyStepSystem.Psi, SafetyStepSystem.alpha,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd,
    ImprovementStepSystem.Czeta]
  have hdes := S.improved_descent t
  have hdrift := S.improved_drift t
  have hcontr := S.contraction t
  nlinarith [hdes, hdrift, hcontr, S.two_alpha_Aeta_le,
    S.residual_drop_coeff, S.eps_coeff_bound, S.b_coeff_bound]
```

- [ ] **Step 3：证明 corrected `C_zeta` 上界**

Append:

```lean
theorem ImprovementStepSystem.Czeta_le
    (S : ImprovementStepSystem) :
    S.Czeta ≤ 3 / 4 * S.eta * S.lam ^ 2 := by
  dsimp [ImprovementStepSystem.Czeta]
  nlinarith [S.two_alpha_Aeta_le]
```

- [ ] **Step 4：证明 cumulative improvement budget**

Append:

```lean
theorem ImprovementStepSystem.cumulative_budget
    (S : ImprovementStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Delta
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Pstar
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d
        + S.Czeta * SeqSum T S.zeta := by
  induction T with
  | zero =>
      simp [SeqSum]
      exact sub_nonneg.mpr (S.P_lower 0)
  | succ T ih =>
      rw [SeqSum, Finset.sum_range_succ, SeqSum, Finset.sum_range_succ,
        SeqSum, Finset.sum_range_succ, SeqSum, Finset.sum_range_succ,
        SeqSum, Finset.sum_range_succ, SeqSum, Finset.sum_range_succ]
      have hstep := S.one_step_lyapunov T
      nlinarith [ih, hstep]
```

- [ ] **Step 5：连接到现有 `ImprovementBudget`**

Append:

```lean
def ImprovementStepSystem.toBudget (S : ImprovementStepSystem) (T : ℕ) :
    ImprovementBudget T where
  eta := S.eta
  lam := S.lam
  CR := S.CR
  Psi0 := S.Psi 0
  Pstar := S.Pstar
  Ceps := S.Ceps
  Cb := S.Cb
  Cd := S.Cd
  Czeta := S.Czeta
  Gsq := S.Gsq
  R := S.R
  Delta := S.Delta
  eps := S.eps
  b := S.b
  d := S.d
  zeta := S.zeta
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  CR_pos := S.CR_pos
  Gsq_nonneg := S.Gsq_nonneg
  R_nonneg := S.R_nonneg
  Delta_nonneg := S.Delta_nonneg
  cumulative_budget := S.cumulative_budget T

theorem ImprovementStepSystem.gradient_improvement_average_bound
    (S : ImprovementStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq
      + 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Delta)
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ))
        + 4 * S.Czeta * SeqSum T S.zeta / (S.eta * (T : ℝ)) := by
  exact ImprovementBudget.gradient_improvement_average_bound hT (S.toBudget T)

theorem ImprovementStepSystem.residual_average_bound
    (S : ImprovementStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Czeta * SeqSum T S.zeta / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  exact ImprovementBudget.residual_average_bound hT (S.toBudget T)

end

end OUSVRBLO
```

- [ ] **Step 6：公开导入并构建**

Modify `OUSVRBLO.lean`:

```lean
import OUSVRBLO.ScalarFacts
import OUSVRBLO.LyapunovBudget
import OUSVRBLO.SafetyDescent
import OUSVRBLO.ImprovementDescent
```

Run:

```powershell
lake build OUSVRBLO.ImprovementDescent
lake build
```

Expected:

```text
Build completed successfully
```

### Task 2.2：形式化 proxy calibration certificate

**Files:**
- Create: `OUSVRBLO/ProxyCertificate.lean`
- Modify: `OUSVRBLO.lean`

- [ ] **Step 1：创建 proxy comparison theorem**

Create `OUSVRBLO/ProxyCertificate.lean`:

```lean
import Mathlib

namespace OUSVRBLO

noncomputable section

structure ProxyComparison where
  eO : ℝ
  eB : ℝ
  ehatO : ℝ
  ehatB : ℝ
  DeltaHat : ℝ
  rho : ℝ
  rho_nonneg : 0 ≤ rho
  calibO_abs : |ehatO - eO| ≤ rho
  calibB_abs : |ehatB - eB| ≤ rho
  proxy_improves : ehatO ≤ ehatB - DeltaHat

theorem ProxyComparison.true_error_improves
    (C : ProxyComparison) :
    C.eO ≤ C.eB - C.DeltaHat + 2 * C.rho := by
  have hO : C.eO ≤ C.ehatO + C.rho := by
    have h := abs_le.mp C.calibO_abs
    linarith [h.1]
  have hB : C.ehatB ≤ C.eB + C.rho := by
    have h := abs_le.mp C.calibB_abs
    linarith [h.2]
  linarith [hO, hB, C.proxy_improves]

structure ProxyR2Plus where
  CR : ℝ
  Rhat : ℝ
  b : ℝ
  eO : ℝ
  eB : ℝ
  DeltaHat : ℝ
  rho : ℝ
  baseline_bound : eB ≤ CR * Rhat + b
  proxy_bound : eO ≤ eB - DeltaHat + 2 * rho

theorem ProxyR2Plus.r2plus
    (C : ProxyR2Plus) :
    C.eO ≤ C.CR * C.Rhat + C.b - C.DeltaHat + 2 * C.rho := by
  nlinarith [C.baseline_bound, C.proxy_bound]

end

end OUSVRBLO
```

- [ ] **Step 2：公开导入并构建**

Modify `OUSVRBLO.lean`:

```lean
import OUSVRBLO.ScalarFacts
import OUSVRBLO.LyapunovBudget
import OUSVRBLO.SafetyDescent
import OUSVRBLO.ImprovementDescent
import OUSVRBLO.ProxyCertificate
```

Run:

```powershell
lake build OUSVRBLO.ProxyCertificate
lake build
```

Expected:

```text
Build completed successfully
```

- [ ] **Step 3：阶段二验收**

Run:

```powershell
bash scripts/check_no_placeholder.sh
```

Expected:

```text
exit code 0
```

Run:

```powershell
git add OUSVRBLO/ImprovementDescent.lean OUSVRBLO/ProxyCertificate.lean OUSVRBLO.lean
git commit -m "feat: verify full interface theorem"
```

Expected:

```text
[main ...] feat: verify full interface theorem
```

---

## 阶段三：完整细致验证

阶段三不是为了替代阶段一和阶段二，而是把当前 hypotheses 中可被抽象证明的部分继续下沉。这个阶段应按收益排序推进，每个子任务单独可合并。

### Task 3.1：从 smoothness 推出 inexact descent

**Files:**
- Create: `OUSVRBLO/AnalyticInterfaces.lean`
- Modify: `OUSVRBLO.lean`

- [ ] **Step 1：定义抽象 smoothness 接口**

Create `OUSVRBLO/AnalyticInterfaces.lean`:

```lean
import Mathlib

namespace OUSVRBLO

noncomputable section

structure SmoothDescentScalar where
  eta : ℝ
  LP : ℝ
  Gsq : ℝ
  Esq : ℝ
  stepSq : ℝ
  Pnow : ℝ
  Pnext : ℝ
  eta_pos : 0 < eta
  step_nonneg : 0 ≤ stepSq
  eta_le_inv_LP : LP * eta ≤ 1
  smooth_step :
    Pnext ≤ Pnow
      - eta / 2 * Gsq
      + eta / 2 * Esq
      - eta / 2 * (1 - LP * eta) * stepSq

theorem SmoothDescentScalar.drop_nonpositive_step
    (S : SmoothDescentScalar) :
    S.Pnext ≤ S.Pnow - S.eta / 2 * S.Gsq + S.eta / 2 * S.Esq := by
  have hcoef : 0 ≤ S.eta / 2 * (1 - S.LP * S.eta) := by
    nlinarith [S.eta_pos, S.eta_le_inv_LP]
  have hterm : 0 ≤ S.eta / 2 * (1 - S.LP * S.eta) * S.stepSq := by
    exact mul_nonneg hcoef S.step_nonneg
  nlinarith [S.smooth_step, hterm]

end

end OUSVRBLO
```

This scalar lemma captures the algebraic part of Section 6 Step 1. A later refinement can replace scalar `Gsq`, `Esq`, and `stepSq` with normed-space objects.

- [ ] **Step 2：公开导入并构建**

Modify `OUSVRBLO.lean`:

```lean
import OUSVRBLO.ScalarFacts
import OUSVRBLO.LyapunovBudget
import OUSVRBLO.SafetyDescent
import OUSVRBLO.ImprovementDescent
import OUSVRBLO.ProxyCertificate
import OUSVRBLO.AnalyticInterfaces
```

Run:

```powershell
lake build OUSVRBLO.AnalyticInterfaces
```

Expected:

```text
Build completed successfully
```

### Task 3.2：形式化 residual-to-gradient sufficient condition

**Files:**
- Modify: `OUSVRBLO/AnalyticInterfaces.lean`

- [ ] **Step 1：加入 Lipschitz/error-bound 推导**

Append before the final `end` lines:

```lean
structure ResidualGradientInterface where
  Lxxi : ℝ
  CEB : ℝ
  R : ℝ
  nu : ℝ
  gradErrSq : ℝ
  Lxxi_nonneg : 0 ≤ Lxxi
  CEB_nonneg : 0 ≤ CEB
  R_nonneg : 0 ≤ R
  nu_nonneg : 0 ≤ nu
  grad_lipschitz_error :
    gradErrSq ≤ Lxxi ^ 2 * (CEB * R + nu)

def ResidualGradientInterface.CR (S : ResidualGradientInterface) : ℝ :=
  S.Lxxi ^ 2 * S.CEB

def ResidualGradientInterface.b (S : ResidualGradientInterface) : ℝ :=
  S.Lxxi ^ 2 * S.nu

theorem ResidualGradientInterface.r2_bound
    (S : ResidualGradientInterface) :
    S.gradErrSq ≤ S.CR * S.R + S.b := by
  dsimp [ResidualGradientInterface.CR, ResidualGradientInterface.b]
  nlinarith [S.grad_lipschitz_error]
```

- [ ] **Step 2：构建**

Run:

```powershell
lake build OUSVRBLO.AnalyticInterfaces
```

Expected:

```text
Build completed successfully
```

### Task 3.3：定义局部正则化 surrogate 的抽象层

**Files:**
- Create: `OUSVRBLO/LocalSurrogate.lean`
- Modify: `OUSVRBLO.lean`

- [ ] **Step 1：创建局部 surrogate 结构**

Create `OUSVRBLO/LocalSurrogate.lean`:

```lean
import Mathlib

namespace OUSVRBLO

noncomputable section

structure LocalRegularizedSurrogate where
  X : Type
  Y : Type
  trainLoss : X → Y → ℝ
  distSqToRef : Y → ℝ
  rho : ℝ
  rho_nonneg : 0 ≤ rho

def LocalRegularizedSurrogate.h
    (S : LocalRegularizedSurrogate) (x : S.X) (xi : S.Y) : ℝ :=
  S.trainLoss x xi + S.rho / 2 * S.distSqToRef xi

structure ValueFunctionInterface where
  X : Type
  Y : Type
  h : X → Y → ℝ
  v : X → ℝ
  response : X → Y
  value_eq_response : ∀ x, v x = h x (response x)

end

end OUSVRBLO
```

This file records the local regularized value-response model without claiming global neural-network optimality.

- [ ] **Step 2：公开导入并构建**

Modify `OUSVRBLO.lean`:

```lean
import OUSVRBLO.ScalarFacts
import OUSVRBLO.LyapunovBudget
import OUSVRBLO.SafetyDescent
import OUSVRBLO.ImprovementDescent
import OUSVRBLO.ProxyCertificate
import OUSVRBLO.AnalyticInterfaces
import OUSVRBLO.LocalSurrogate
```

Run:

```powershell
lake build OUSVRBLO.LocalSurrogate
lake build
```

Expected:

```text
Build completed successfully
```

- [ ] **Step 3：阶段三验收**

Run:

```powershell
bash scripts/check_no_placeholder.sh
lake build
```

Expected:

```text
Build completed successfully
```

Run:

```powershell
git add OUSVRBLO/AnalyticInterfaces.lean OUSVRBLO/LocalSurrogate.lean OUSVRBLO.lean
git commit -m "feat: add analytic interface verification"
```

Expected:

```text
[main ...] feat: add analytic interface verification
```

---

## 文档与验收

### Task 4.1：写中文阶段说明

**Files:**
- Create: `docs/LEAN_VERIFICATION_PHASES.md`
- Modify: `README.md`
- Modify: `docs/FORMALIZATION_SCOPE.md`

- [ ] **Step 1：创建中文阶段说明**

Create `docs/LEAN_VERIFICATION_PHASES.md`:

```markdown
# Lean 形式验证阶段说明

## 阶段一：核心定理验证

验证主定理的 Lyapunov budget 结构：one-step descent、finite-horizon summation、averaged stationarity bound、averaged residual bound。

该阶段回答：在附件列出的接口假设成立时，主定理的收敛预算是否正确。

## 阶段二：整体验证

验证 enhanced theorem、corrected `C_zeta`、proxy calibration certificate，并把它们连接到现有 averaged bounds。

该阶段回答：附件修订版证明从 safety 到 upper-gradient improvement 是否完整闭合。

## 阶段三：完整细致验证

逐步形式化若干接口假设的充分条件，例如 smooth descent、residual-to-gradient error bound、local regularized surrogate。

该阶段回答：哪些假设可以继续从更基础的数学条件推出。

## 不证明的内容

本项目不证明 general nonconvex BLO global convergence，也不证明 original BLO KKT convergence。LLM/LoRA 场景中的工程条件以局部 surrogate 和接口假设方式表达。
```

- [ ] **Step 2：更新 `docs/FORMALIZATION_SCOPE.md`**

Replace it with:

```markdown
# Formalization scope

This repository formalizes the proof skeleton of the revised OUSVR-BLO online value-anchor theorem.

## Coverage map

- Sections 1-4: represented as hypotheses and abstract interfaces.
- Section 5: represented by `SafetyBudget` and `SafetyStepSystem`.
- Section 6: represented by `SafetyStepSystem.one_step_lyapunov` and `SafetyStepSystem.cumulative_budget`.
- Sections 7-8: represented by `ImprovementBudget` and `ImprovementStepSystem`.
- Section 9: represented by `ImprovementStepSystem.Czeta` and `ImprovementStepSystem.Czeta_le`.
- Section 10: represented by `ProxyComparison.true_error_improves` and `ProxyR2Plus.r2plus`.
- Sections 11-14: documented as modeling interpretation and claim boundary.

## Boundary

Lean checks the algebraic proof skeleton, coefficient flow, finite-horizon sums, and averaged bounds. Smoothness, value-function differentiability, residual contraction, residual drift compatibility, and LLM/LoRA local response conditions remain explicit hypotheses unless a later phase proves sufficient conditions for them.
```

- [ ] **Step 3：更新 README**

Add this section to `README.md`:

```markdown
## Verification phases

The project is organized into three Lean verification phases:

1. Core theorem verification: safety Lyapunov budget and averaged bounds.
2. Whole-proof verification: enhanced theorem, corrected `C_zeta`, and proxy certificate.
3. Detailed verification: sufficient-condition lemmas for selected analytic interfaces.

The first two phases are the main target for validating the manuscript proof structure. The third phase is an optional deeper mathematical formalization layer.
```

- [ ] **Step 4：构建并检查文档**

Run:

```powershell
rg --line-number "阶段一|阶段二|阶段三|C_zeta|proxy|KKT" README.md docs
lake build
```

Expected:

```text
README.md:...
docs/...
Build completed successfully
```

- [ ] **Step 5：提交文档**

Run:

```powershell
git add README.md docs/FORMALIZATION_SCOPE.md docs/LEAN_VERIFICATION_PHASES.md
git commit -m "docs: describe Lean verification phases"
```

Expected:

```text
[main ...] docs: describe Lean verification phases
```

---

## 最终验收

### Task 5.1：完整构建与证明占位检查

**Files:**
- No source edits unless verification exposes a concrete issue.

- [ ] **Step 1：完整构建**

Run:

```powershell
lake build
```

Expected:

```text
Build completed successfully
```

- [ ] **Step 2：占位证明检查**

Run:

```powershell
bash scripts/check_no_placeholder.sh
```

Expected:

```text
exit code 0
```

- [ ] **Step 3：确认 git 状态**

Run:

```powershell
git status --short
```

Expected:

```text
working tree clean
```

- [ ] **Step 4：如果需要，推送到远端触发 CI**

Run with network access:

```powershell
git push origin main
```

Expected:

```text
main -> main
```

---

## 决策点

阶段一完成后：

- 如果目标是确认主定理 budget 正确，可以暂停。
- 如果目标是确认附件修订版整体 proof claim 正确，继续阶段二。

阶段二完成后：

- 如果目标是减少人工精读证明的工作量，可以暂停。
- 如果目标是把更多假设本身也纳入 Lean，可进入阶段三。

阶段三完成后：

- 可以考虑继续把 scalar abstraction 提升到 normed-space abstraction。
- 可以考虑把 value-function envelope theorem 作为独立长期任务。

## 自检清单

- 计划已改为中文说明。
- 计划明确拆成核心定理验证、整体验证、完整细致验证三个层级。
- 每个阶段都有验收命令和预期输出。
- 阶段一和阶段二优先服务用户目标：减少人工细致验证证明的精力。
- 阶段三不夸大结论，不声称证明真实 LLM 微调自动满足所有假设。
