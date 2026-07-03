import ChaosvmProofs.Definitions.SemShare

/-! # T16: R_run 不变性 (Φₜ 共轭)

## 定理陈述

`decode_i41(bridge_i41(c0, anchor, c1_t, c2, σ, DDM, q_σ, q_D))` 的值
与 `σ`、`DDM`、`c1_t` 无关，只取决于 `c0`, `anchor`, `c2`, `q_σ`, `q_D`。

在 VM 执行中：
- `c0`, `alpha`, `edge` 来自编码指令（构建时确定）
- `anchor = lo8(t_ddm[alpha])` 来自构建时表格和指令 alpha 字段
- `c2 = c2_from_edge(edge)` 来自指令 edge 字段
- `σ`, `DDM`, `c1_t` 取决于 R_run 参数 (r0, r1, m) 和当前执行状态

因此 v_t 对任意 R_run 输出相同值 — R_run 不变性成立。
-/

/-- 引理: decode(bridge(c0, ...)) = c0 ⊕ permute(anchor,0) ⊕ permute(c2,0) — 与 σ, DDM, c1_t 无关。
    
    证明: 将 c0 表示为 encode(u) 的形式后用 T08 (bridge_decode_invariant)。 -/
theorem T16_decode_bridge_general (c0 anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) :
    decode_i41 (bridge_i41 c0 anchor c1_t c2 σ DDM q_sigma q_ddm) c1_t c2 σ DDM q_sigma q_ddm
    = c0 ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm := by
  let u := c0 ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm
  have hu : encode_c0_i41 u anchor c2 q_sigma q_ddm = c0 := by
    unfold encode_c0_i41
    dsimp [u]
    calc
      (c0 ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm) ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm
          = c0 ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm := rfl
      _ = c0 ^^^ ((permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm ^^^ permute anchor 0 q_sigma) ^^^ permute c2 0 q_ddm) := by
        simp [Nat.xor_assoc]
      _ = c0 ^^^ (((permute anchor 0 q_sigma ^^^ permute anchor 0 q_sigma) ^^^ permute c2 0 q_ddm) ^^^ permute c2 0 q_ddm) := by
        have h_swap : permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm ^^^ permute anchor 0 q_sigma
            = permute anchor 0 q_sigma ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm := by
          calc
            permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm ^^^ permute anchor 0 q_sigma
                = permute anchor 0 q_sigma ^^^ (permute c2 0 q_ddm ^^^ permute anchor 0 q_sigma) := by rw [Nat.xor_assoc]
            _ = permute anchor 0 q_sigma ^^^ (permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm) := by rw [Nat.xor_comm (permute c2 0 q_ddm) (permute anchor 0 q_sigma)]
            _ = (permute anchor 0 q_sigma ^^^ permute anchor 0 q_sigma) ^^^ permute c2 0 q_ddm := by rw [← Nat.xor_assoc]
            _ = permute anchor 0 q_sigma ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm := rfl
        rw [h_swap]
      _ = c0 ^^^ ((0 ^^^ permute c2 0 q_ddm) ^^^ permute c2 0 q_ddm) := by simp
      _ = c0 ^^^ (permute c2 0 q_ddm ^^^ permute c2 0 q_ddm) := by simp
      _ = c0 ^^^ 0 := by simp
      _ = c0 := by simp
  calc
    decode_i41 (bridge_i41 c0 anchor c1_t c2 σ DDM q_sigma q_ddm) c1_t c2 σ DDM q_sigma q_ddm
        = decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2 q_sigma q_ddm) anchor c1_t c2 σ DDM q_sigma q_ddm)
                     c1_t c2 σ DDM q_sigma q_ddm := by rw [hu]
    _ = u := bridge_decode_invariant u anchor c1_t c2 σ DDM q_sigma q_ddm
    _ = c0 ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm := rfl

/-- T16: R_run 不变性 (Φₜ 共轭) — v_t 对任意两组状态参数输出相同值。

    `decode_i41(bridge_i41(c0, anchor, c1_t, c2, σ, DDM, ...))` 
    对于任意两组 (σ₁, DDM₁, c1_t₁) 和 (σ₂, DDM₂, c1_t₂) 结果相同。
    因此 v_t 不依赖于 R_run（即运行时的随机/熵源参数）。 -/
theorem T16_rrun_invariance (c0 anchor c2 : Nat) (q_sigma q_ddm : QAvalancheConfig)
    (σ₁ σ₂ DDM₁ DDM₂ c1_t₁ c1_t₂ : Nat) :
    decode_i41 (bridge_i41 c0 anchor c1_t₁ c2 σ₁ DDM₁ q_sigma q_ddm) c1_t₁ c2 σ₁ DDM₁ q_sigma q_ddm
    = decode_i41 (bridge_i41 c0 anchor c1_t₂ c2 σ₂ DDM₂ q_sigma q_ddm) c1_t₂ c2 σ₂ DDM₂ q_sigma q_ddm := by
  calc
    decode_i41 (bridge_i41 c0 anchor c1_t₁ c2 σ₁ DDM₁ q_sigma q_ddm) c1_t₁ c2 σ₁ DDM₁ q_sigma q_ddm
        = c0 ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm :=
      T16_decode_bridge_general c0 anchor c1_t₁ c2 σ₁ DDM₁ q_sigma q_ddm
    _ = decode_i41 (bridge_i41 c0 anchor c1_t₂ c2 σ₂ DDM₂ q_sigma q_ddm) c1_t₂ c2 σ₂ DDM₂ q_sigma q_ddm := by
      rw [T16_decode_bridge_general c0 anchor c1_t₂ c2 σ₂ DDM₂ q_sigma q_ddm]
