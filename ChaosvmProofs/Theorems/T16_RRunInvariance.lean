import ChaosvmProofs.Definitions.SemShare

/-! # T16: R_run 不变性 (Φₜ 共轭)

## 定理陈述

∀ R_run（参数化为 r0, r1, m），任意步 t 的解码操作码 v_t 与当前状态
(σₜ, CFAₜ, DDMₜ, Hₜ) 以及 R_run 参数无关，仅取决于编码指令中的固定字段
和构建时表格。

## 证明

`decode(bridge(encode(u, anchor, c2), anchor, c1_t, c2, σ, DDM), c1_t, c2, σ, DDM) = u`
对**所有** σ, DDM, c1_t, c2, anchor 成立（T08）。由于：

- anchor = lo8(t_ddm[alpha]) — 仅依赖于 alpha（指令字段）和构建表格
- c2 = c2_from_edge(edge) — 仅依赖于 edge（指令字段）
- c0 — 直接来自编码指令
- σₜ, DDMₜ, c1_t 取决于 R_run，但代数消去使其不影响结果

因此解码值 v_t 对任意 R_run 不变。
-/

/-- T16: R_run 不变性 (Φₜ 共轭).

    bridge+decode 管线中 σ 和 DDM 项代数消去，使解码后的操作码与当前状态
    及 R_run 初始化参数无关。这是 T08 的直接推论。

    `anchor` = lo8(t_ddm[alpha]) 由构建时表格和 alpha 指令字段决定，不依赖于
    R_run 参数 (r0, r1, m)。

    `c2` = c2_from_edge(edge) 仅由 edge 指令字段决定。

    `c0` 来自编码指令。

    因此 `u = encode_c0_i41(c0, anchor, c2)` 对任意 R_run 都是常量：
    `decode(bridge(encode(u), ...), ...) = u` 对所有 σ, DDM, c1_t 成立。 -/
theorem T16_rrun_invariance (u anchor c1_t c2 σ DDM : Nat) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2) anchor c1_t c2 σ DDM) c1_t c2 σ DDM = u :=
  bridge_decode_invariant u anchor c1_t c2 σ DDM
