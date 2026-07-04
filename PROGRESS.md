# ChaosVM Proofs — 形式化证明进度

> Lean 4.30，仅依赖 `Init.Omega`，无 Mathlib。

## 已完成定理

| 定理 | 文件 | 状态 |
|------|------|------|
| T01–T12 (基础定义 + 量子化架构) | `Definitions/` | ✅ Stable |
| T13 (Init Divergence) — 4 字段条件发散 | `Theorems/T13_InitDivergence.lean` | ✅ |
| T14 (Poison Cascade) — σ/CFA/DDM 链单射 + H→δ 级联 | `Theorems/T14_PoisonCascade.lean` | ✅ |
| T15 (No Single Exit) — 架构审计 + 类型系统保证 | `Theorems/T15_NoSingleExit.lean` | ✅ 审计 + 形式化 |
| T16 (R_run Invariance) — decode + bridge 不变性 | `Theorems/T16_RRunInvariance.lean` | ✅ |
| T17 (Functional Equivalence) — v_t 输出与 VM 状态无关 | `Theorems/T17_FunctionalEquivalence.lean` | ✅ |
| T17-full (Full Decode Equivalence) — decode_full（包含 phi_op_inv）输出无关性 | `Theorems/T17_FunctionalEquivalence.lean` | ✅ |
| T08-full (Full Roundtrip) — bridge+encode+phi_op_inv 完整管道 | `Theorems/T08_BridgeDecodeInvariant.lean` | ✅ |
| K3 (Bridge State Dependency) — σ/DDM/c1_t 各不相同 | `Theorems/K3_BridgeStateDependency.lean` | ✅ |
| K4 (Share Indispensability) — c2/c0 为零时 != u | `Theorems/K4_ShareIndispensability.lean` | ✅ |

## 构建状态

`lake build ChaosvmProofs` — 38 jobs, 0 errors, 0 warnings ✅

## 待补强

| 项目 | 优先级 | 工作量 | 状态 |
|------|--------|--------|------|
| **L1**: phi_op_inv 模型补齐 → T17 重述 | P1 | 2–3h | ✅ 已完成 |
| **L2**: decode 状态依赖非线性项 (Rust+Lean) | P2 | 4–6h | ⏭ 跳过（成本/收益比不理想） |
| **L3**: T15 形式化 (NoExit typeclass + 证明) | P3 | 3–5h | ✅ 已完成（引用 Init.lean 已有形式化） |

## 关键修复记录

### 2026-07-04 — L1/L3 闭包 + T15 形式化

**L1: phi_op_inv 模型补齐**:
1. 新建 `Definitions/PhiPerm.lean`：phi/phi_op_inv 仿射双射 (17x+43)，decode_full，full_bridge_decode_invariant
2. 更新 T17：新增 T17_functional_equivalence_full（decode_full 输出无关性）
3. 更新 T08：新增 T08_full_roundtrip（完整管线 roundtrip）
4. 提交：`41c0803`

**L3: T15 形式化**:
1. 更新 T15_NoSingleExit.lean：引用 Init.lean 已有形式化，说明 NoExit 由类型系统保证
2. 更新审计报告：L1 闭包记录 + L2 跳过决策 + 定理覆盖总览
3. L2 决策：评估后跳过（成本 6-8h，收益有限，XOR 对消是有意设计）

**审计报告更新**:
- 38 jobs 全部编译通过
- 定理覆盖总览表（T01–T17 + K1–K4 全部 ✅）

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
