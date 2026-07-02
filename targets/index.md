# ChaosVM v2 形式化证明目标总览

## 依赖层次

```
Level 1 ── 独立原语双射性
  T01  P(x,s) 是 u8 上的双射
  T02  affine_map(r,a,b) 是 u8 上的双射
  T03  c2_from_edge 良定义
  T04  decompose_safe 确保 a_rd/a_ra/a_rb 为奇数

Level 2 ── G 混合器
  T05  g_init 确定型
  T06  g_rounds 确定型
  T07  G 混合器是 u64³ → u64² 的双射

Level 3 ── 桥接+解码不变性
  T08  bridge+decode 管线满足 ∀σ,DDM: decode(bridge(encode(op))) = op ✅

Level 4 ── 状态演化确定型
  T09  update_state 确定型
  T10  step() 确定型状态转移
  T11  run_program 确定型

Level 5 ── 反篡改性质
  T12  Init 确定型: 相同 K_build+R_run → 相同 InitState
  T13  Init 发散: P≠0 → 初始状态不同
  T14  投毒级联: P≠0 → N 步后状态发散
  T15  无单一出口架构性质

Level 6 ── R_run 不变性 (Φₜ 共轭)
  T16  ∀R_run: step t 译码 opcode = Φ_B(op_i)

Level 7 ── 功能等价性
  T17  ∀R_run₁,R_run₂: 相同程序+输入 → 相同最终语义输出
```

## 完成状态

| 定理 | 状态 | Lean 证明 |
|------|------|-----------|
| T01 P_mod 双射 | ✅ 已证明 (Injective ∧ Surjective) | `Definitions/Permutation.lean` |
| T02 affine_map 双射 | ✅ 已证明 (Injective ∧ Surjective) | `Definitions/Permutation.lean` |
| T03 c2_from_edge 良定义 | ✅ 已证明 | `Definitions/EdgeEncoding.lean` |
| T04 decompose_safe 确保奇数 | ✅ 已证明 | `Definitions/ZLayout.lean` |
| T05 g_init 确定型 | 平凡 | `Definitions/GMixer.lean` |
| T06 g_rounds 确定型 | 平凡 | `Definitions/GMixer.lean` |
| T07 G 混合器双射 | 待证明 🏗 | `Definitions/GMixer.lean` |
| T08 bridge+decode 不变性 | ✅ 已证明 (with abstraction notes) | `Definitions/SemShare.lean` |
| T09 update_state 确定型 | 平凡 | `Definitions/StateUpdate.lean` |
| T10 step 确定型 | 待证明 | `Theorems/T10_StepDeterministic.lean` |
| T11 run_program 确定型 | 待证明 | `Theorems/T11_RunProgramDeterministic.lean` |
| T12 Init 确定型 | 平凡 | `Definitions/Init.lean` |
| T13 Init poision 发散 | ✅ 已证明 | `Definitions/Init.lean` |
| T14 投毒级联 | 待证明 | `Theorems/T14_PoisonCascade.lean` |
| T15 无单一出口 | 待证明 | `Theorems/T15_NoSingleExit.lean` |
| T16 R_run 不变性 | 待证明 | `Theorems/T16_RRunInvariance.lean` |
| T17 功能等价性 | 待证明 | `Theorems/T17_FunctionalEquivalence.lean` |

## 文件映射

| Lean 文件 | Rust 源 | 覆盖原语 |
|-----------|---------|---------|
| `Definitions/Permutation.lean` | `sem_share.rs` `reg_map.rs` | P(x,s), affine_map |
| `Definitions/QAvalanche.lean` | `g_mixer.rs` | q_avalanche |
| `Definitions/GMixer.lean` | `g_mixer.rs` | g_init, g_rounds, g_mix |
| `Definitions/HIndex.lean` | `h_index.rs` | h_sigma, h_cfa, h_ddm |
| `Definitions/SemShare.lean` | `sem_share.rs` `encoder.rs` | encode/bridge/decode |
| `Definitions/StateUpdate.lean` | `state.rs` | update_h, update_state |
| `Definitions/ZLayout.lean` | `z_layout.rs` | decompose, decompose_safe |
| `Definitions/EdgeEncoding.lean` | `edge_encoding.rs` | c2_from_edge |
| `Definitions/Init.lean` | `init.rs` | init, init_poisoned |
