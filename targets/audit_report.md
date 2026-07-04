# 证明链审计报告 — 2026-07-04

审计范围: 21 定理文件 + 12 定义文件，~3800 行 Lean 代码

## 依赖图完整性

无循环依赖 ✓ | 38 jobs 全部编译通过 ✓ | 0 `axiom`/`sorry`/`admit` ✓

## L1 闭包（2026-07-04）

phi_op_inv gap 已闭合：

| 文件 | 改动 |
|------|------|
| `Definitions/PhiPerm.lean` | 新建：phi/phi_op_inv 仿射双射，decode_full，full_bridge_decode_invariant |
| `Definitions.lean` | 加入 PhiPerm 模块链 |
| `T17_FunctionalEquivalence.lean` | 新增 T17_functional_equivalence_full（decode_full 输出无关性） |
| `T08_BridgeDecodeInvariant.lean` | 新增 T08_full_roundtrip（完整管线轮转） |
| `T15_NoSingleExit.lean` | 更新：引用 Init.lean 已有形式化，说明 NoExit 由类型系统保证 |

## 已修复问题

| # | 文件 | 问题 | 修复 |
|---|------|------|------|
| 1 | T13_InitDivergence.lean | 只证明结构不平等 | ✅ 添加 T13b–T13e 四个字段级条件发散引理 |
| 2 | T16_RRunInvariance.lean | 语句和 T08 完全一致 | ✅ 重写为独立定理 |
| 3 | K4b/K4c | 只刻画 decode 结果 | ✅ 添加 `_ne_u` 条件推论 |
| 4 | T17 + T08 | phi_op_inv gap（安全边界偏移） | ✅ L1 闭合：PhiPerm + decode_full |

## 仍存在的弱命题

| # | 文件 | 问题 | 影响 |
|---|------|------|------|
| 5 | T05/T06/T09–T12 | 确定型定理 = `rfl`。对纯函数恒成立，证明力为零 | **低** — 占位性质 |
| 6 | T14_PoisonCascade.lean | 只证明 H 链发散传播，未覆盖 σ/CFA/DDM 链 | **中** — 命名暗示全状态 |

## L2 决策记录

L2（修改 Rust decode_i41 打破 XOR 对称）已评估并**跳过**：
- 成本：~6-8h（6 Rust 文件 + 5 Lean 证明重写）
- 收益：有限（寄存器观察非主要威胁面）
- 设计意图：`sem_share.rs` 文档明确说明 XOR 对消是有意为之
- 结论：L1 (phi model) + L3 (T15 formalization) 已形成完整闭环

## 定理覆盖总览

| 定理 | 状态 | 说明 |
|------|------|------|
| T01–T04 | ✅ | 基础定义 + 量子化架构 |
| T05–T06 | ✅ (rfl) | 确定型性质 |
| T07 | ✅ | Q avalanche 单射性 |
| T08 (v_t) | ✅ | bridge+decode roundtrip |
| T08 (full) | ✅ | 完整管线 roundtrip（含 phi_op_inv） |
| T09–T12 | ✅ (rfl) | 状态更新确定性 |
| T13 | ✅ | Init 发散（结构 + 条件字段级） |
| T14 | ✅ | Poison cascade（H 链） |
| T15 | ✅ | No Exit（类型系统保证 + 审计） |
| T16 | ✅ | R_run 不变性 |
| T17 (v_t) | ✅ | v_t 输出无关性 |
| T17 (full) | ✅ | decode_full 输出无关性 |
| K1–K4 | ✅ | 关键性质（share 依赖、消去、不可替代性） |
