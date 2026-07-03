# ChaosVM Proofs — 形式化证明进度

> Lean 4.30，仅依赖 `Init.Omega`，无 Mathlib。

## 已完成定理

| 定理 | 文件 | 状态 |
|------|------|------|
| T01–T12 (基础定义 + 量子化架构) | `Definitions/` | ✅ Stable |
| T13 (Init Divergence) — 4 字段条件发散 | `Theorems/T13_InitDivergence.lean` | ✅ |
| T14 (Poison Cascade) — σ/CFA/DDM 链单射 + H→δ 级联 | `Theorems/T14_PoisonCascade.lean` | ✅ |
| T15 — pending | — | ⬜ |
| T16 (R_run Invariance) — decode + bridge 不变性 | `Theorems/T16_RRunInvariance.lean` | ✅ |
| T17 (Functional Equivalence) — v_t 输出与 VM 状态无关 | `Theorems/T17_FunctionalEquivalence.lean` | ✅ |
| K3 (Bridge State Dependency) — σ/DDM/c1_t 各不相同 | `Theorems/K3_BridgeStateDependency.lean` | ✅ |
| K4 (Share Indispensability) — c2/c0 为零时 != u | `Theorems/K4_ShareIndispensability.lean` | ✅ |

## 构建状态

`lake build ChaosvmProofs` — 37 jobs, 0 errors, 0 warnings ✅

## 关键修复记录

### 2026-07-03 — T14 完整实现 (P2a-d + P3a-f)

**新增引理**：
1. **`add_mod64_inj`** (P2a) — `(a+k) % 2^64 = (b+k) % 2^64 → a = b` (via `omega`)
2. **`sigma_next_inj_in_sigma`** (P2b) — `rotl(σ1+d,17)^^^d_D ≠ rotl(σ2+d,17)^^^d_D` when σ1≠σ2
3. **`ddm_next_inj_in_ddm`** (P2c) — `rotl(DDM1+d,47)^^^d_C ≠ rotl(DDM2+d,47)^^^d_C` when DDM1≠DDM2
4. **`cfa_next_inj_in_cfa`** (P2d) — CFA 链模加单射 (rotl64_inj + xor_inj)
5. **P3a-c** — 对称包装器 (d_σ/d_C/d_D 各使其 next 值不同)
6. **P3d-f** — H→δ 横向级联 (d_σ/d_C/d_D 各不同通过 qAvalanche_inj)
7. **`xor_quad_cancel`** — XOR 四次项消除引理 (避免 simp 递归循环)

**解决的问题**：
1. **`Nat.xor_left_comm` 不存在** — Lean 4.30 没有此引理；用 `Nat.xor_assoc` + `Nat.xor_comm` 链或 `xor_quad_cancel` 替代
2. **`xor_cancel_right` 作用域** — 定义在 `Init.lean` 中，T14 需显式 import
3. **递归深度溢出** — `:=` 直接统一调用含 `2^64` 的定理会导致 kernel 递归；改用 `have` + `simpa` 的 `by` 块模式
4. **`calc` 嵌套语法** — 内层 `calc` 不能在 `calc` 步骤的 `by` 块中直接使用；需提取为独立 `h_reassoc` 引理
5. **`omega` 递归** — 对称包装器中用 `(Nat.add_comm σ d_σ1).symm ▸ hsum1` 替代 `omega`
