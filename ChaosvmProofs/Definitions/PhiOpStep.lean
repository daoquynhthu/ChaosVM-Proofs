import ChaosvmProofs.Definitions.Helpers
import ChaosvmProofs.Definitions.QAvalanche

open Nat

/-! # Per-step Φ_op 置换 (Rust: `phi_op_inv_step`)

架构文档 Section 4.6 描述动态坐标映射：opₜ = Φ_op,t⁻¹(uₜ)。
本文件定义 per-step phi_op_inv / phi_op，以及 roundtrip 安全属性。
-/

/-- 模 256 奇数乘法逆元查找表。索引 i 对应奇数 2*i+1。 -/
def mod_inv_table : Array Nat :=
  #[1,171,205,183,57,163,197,239,241,27,61,167,41,19,53,223,
    225,139,173,151,25,131,165,207,209,251,29,135,9,243,21,191,
    193,107,141,119,249,99,133,175,177,219,253,103,233,211,245,159,
    161,75,109,87,217,67,101,143,145,187,221,71,201,179,213,127,
    129,43,77,55,185,35,69,111,113,155,189,39,169,147,181,95,
    97,11,45,23,153,3,37,79,81,123,157,7,137,115,149,63,
    65,235,13,247,121,227,5,47,49,91,125,231,105,83,117,31,
    33,203,237,215,89,195,229,15,17,59,93,199,73,51,85,255]

/-- mod_inv_odd: 奇数 a 的模 256 逆元。对偶数返回 0。 -/
def mod_inv_odd (a : Nat) : Nat :=
  mod_inv_table[a / 2]!

/-- mod_inv_odd 对所有奇数 a < 256 正确。 -/
theorem mod_inv_odd_correct : ∀ a < 256, a % 2 = 1 → (a * mod_inv_odd a) % 256 = 1 := by
  native_decide

/-! ## Nat.lor 辅助引理 -/

/-- 若 x < 256 则 x.lor 1 < 256。 -/
theorem lor_one_lt : ∀ x < 256, x.lor 1 < 256 := by
  native_decide

/-- x.lor 1 总是奇数（对 x < 256）。 -/
theorem lor_one_odd : ∀ x < 256, x.lor 1 % 2 = 1 := by
  native_decide

/-! ## 仿射 roundtrip 核心引理 -/

/-- 仿射 roundtrip 核心正向。
    ∀ a < 256, ∀ b < 256, ∀ x < 256, a 为奇数 → roundtrip 成立。 -/
theorem affine_roundtrip_core :
    ∀ a < 256, ∀ b < 256, ∀ x < 256, a % 2 = 1 →
    (mod_inv_odd a * ((a * x + b) % 256 + 256 - b)) % 256 = x := by
  native_decide

/-- 仿射 roundtrip 核心反向。 -/
theorem affine_roundtrip_core_rev :
    ∀ a < 256, ∀ b < 256, ∀ y < 256, a % 2 = 1 →
    (a * ((mod_inv_odd a * (y + 256 - b)) % 256) + b) % 256 = y := by
  native_decide

/-! ## Per-step phi_op / phi_op_inv 定义 -/

/-- Per-step phi_op: 状态依赖的仿射正向映射。 -/
def phi_op_step (x σ DDM H : Nat) (q_op : QAvalancheConfig) : Nat :=
  let mix := qAvalanche (σ ^^^ DDM ^^^ H) q_op
  let a := (Nat.lor (mix % 256) 1)
  let b := (mix / 256) % 256
  (a * x + b) % 256

/-- Per-step phi_op_inv: 状态依赖的仿射逆映射。 -/
def phi_op_inv_step (y σ DDM H : Nat) (q_op : QAvalancheConfig) : Nat :=
  let mix := qAvalanche (σ ^^^ DDM ^^^ H) q_op
  let a := (Nat.lor (mix % 256) 1)
  let b := (mix / 256) % 256
  let a_inv := mod_inv_odd a
  (a_inv * (y + 256 - b)) % 256

/-! ## 有界性引理 -/

/-- phi_op_step 结果有界 (< 256)。 -/
theorem phi_op_step_lt_256 (x σ DDM H : Nat) (q_op : QAvalancheConfig) :
    phi_op_step x σ DDM H q_op < 256 :=
  Nat.mod_lt _ (by decide)

/-- phi_op_inv_step 结果有界 (< 256)。 -/
theorem phi_op_inv_step_lt_256 (y σ DDM H : Nat) (q_op : QAvalancheConfig) :
    phi_op_inv_step y σ DDM H q_op < 256 :=
  Nat.mod_lt _ (by decide)

/-! ## Per-step roundtrip -/

/-- Per-step roundtrip: Φ_op,t⁻¹(Φ_op,t(x)) = x 对 x < 256。 -/
theorem phi_op_inv_step_roundtrip (x σ DDM H : Nat) (q_op : QAvalancheConfig)
    (hx : x < 256) :
    phi_op_inv_step (phi_op_step x σ DDM H q_op) σ DDM H q_op = x := by
  unfold phi_op_step phi_op_inv_step
  have ha : (qAvalanche (σ ^^^ DDM ^^^ H) q_op % 256).lor 1 < 256 :=
    lor_one_lt _ (Nat.mod_lt _ (by decide))
  have hb : (qAvalanche (σ ^^^ DDM ^^^ H) q_op / 256) % 256 < 256 :=
    Nat.mod_lt _ (by decide)
  have ha_odd : (qAvalanche (σ ^^^ DDM ^^^ H) q_op % 256).lor 1 % 2 = 1 :=
    lor_one_odd _ (Nat.mod_lt _ (by decide))
  exact affine_roundtrip_core _ ha _ hb _ hx ha_odd

/-- Per-step roundtrip 反向: Φ_op,t(Φ_op,t⁻¹(y)) = y 对 y < 256。 -/
theorem phi_op_step_inv_roundtrip (y σ DDM H : Nat) (q_op : QAvalancheConfig)
    (hy : y < 256) :
    phi_op_step (phi_op_inv_step y σ DDM H q_op) σ DDM H q_op = y := by
  unfold phi_op_step phi_op_inv_step
  have ha : (qAvalanche (σ ^^^ DDM ^^^ H) q_op % 256).lor 1 < 256 :=
    lor_one_lt _ (Nat.mod_lt _ (by decide))
  have hb : (qAvalanche (σ ^^^ DDM ^^^ H) q_op / 256) % 256 < 256 :=
    Nat.mod_lt _ (by decide)
  have ha_odd : (qAvalanche (σ ^^^ DDM ^^^ H) q_op % 256).lor 1 % 2 = 1 :=
    lor_one_odd _ (Nat.mod_lt _ (by decide))
  exact affine_roundtrip_core_rev _ ha _ hb _ hy ha_odd
