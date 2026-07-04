import ChaosvmProofs.Definitions.SemShare

open Nat

/-! # Φ-置换 (opcode permutation layer)

Rust 的 `phi_op_inv` 层：`v_t` 经过此置换（逆）后才成为实际 opcode。
Lean 模型此前未覆盖此层，T17 证明的安全边界在 `v_t` 而非 `op_u8`。

本文件定义 `phi`/`phi_op_inv`（Fin 256 上的仿射双射），
以及 `decode_full` 包装器（`phi_op_inv ∘ decode_i41`），
作为 T17 gap 闭包的模型基础。

在 Rust 实现中，该置换为构建时随机生成；此处选择仿射双射 `17*x+43`
用于 Lean 可验证性（具体选择不影响任何定理）。
-/

/-- `phi(x) = (17*x + 43) % 256`，Fin 256 上的仿射双射（17 为奇数）。 -/
def phi (x : Nat) : Nat := (17 * x + 43) % 256

/-- `phi_op_inv` 是 `phi` 的逆：`phi_op_inv(y) = (241 * (y + 213)) % 256`，
    其中 `17 * 241 ≡ 1 (mod 256)`。 -/
def phi_op_inv (y : Nat) : Nat := (241 * ((y + 213) % 256)) % 256

theorem phi_lt_256 (x : Nat) : phi x < 256 :=
  Nat.mod_lt _ (by decide)

theorem phi_op_inv_lt_256 (y : Nat) : phi_op_inv y < 256 :=
  Nat.mod_lt _ (by decide)

theorem phi_mod_256 (x : Nat) : phi x = phi (x % 256) := by
  unfold phi
  have h : (17 * x + 43) % 256 = (17 * (x % 256) + 43) % 256 := by
    omega
  rw [h]

theorem phi_op_inv_mod_256 (y : Nat) : phi_op_inv y = phi_op_inv (y % 256) := by
  unfold phi_op_inv
  have h : (241 * ((y + 213) % 256)) % 256 = (241 * (((y % 256) + 213) % 256)) % 256 := by
    omega
  rw [h]

/-- `phi_op_inv ∘ phi = id` 对 `x < 256`。 -/
theorem phi_inverse_bounded : ∀ x < 256, phi_op_inv (phi x) = x := by
  native_decide

/-- `phi ∘ phi_op_inv = id` 对 `y < 256`。 -/
theorem phi_op_inv_inverse_bounded : ∀ y < 256, phi (phi_op_inv y) = y := by
  native_decide

/-- `phi_op_inv ∘ phi = λ x, x % 256`（对任意 Nat）。 -/
theorem phi_inverse (x : Nat) : phi_op_inv (phi x) = x % 256 := by
  calc
    phi_op_inv (phi x) = phi_op_inv (phi (x % 256)) := by rw [phi_mod_256]
    _ = x % 256 := phi_inverse_bounded (x % 256) (Nat.mod_lt x (by decide))

/-- `phi ∘ phi_op_inv = λ y, y % 256`（对任意 Nat）。 -/
theorem phi_op_inv_inverse (y : Nat) : phi (phi_op_inv y) = y % 256 := by
  calc
    phi (phi_op_inv y) = phi (phi_op_inv (y % 256)) := by rw [phi_op_inv_mod_256]
    _ = y % 256 := phi_op_inv_inverse_bounded (y % 256) (Nat.mod_lt y (by decide))

/-- `phi` 在 `Fin 256` 上是 injective（由 `phi_inverse_bounded` 保证）。 -/
theorem phi_injective : ∀ (x y : Fin 256), phi x.val = phi y.val → x = y := by
  intro x y h
  apply Fin.ext
  have hx := phi_inverse_bounded x.val x.is_lt
  have hy := phi_inverse_bounded y.val y.is_lt
  have h_inv : phi_op_inv (phi x.val) = phi_op_inv (phi y.val) := by rw [h]
  rw [hx, hy] at h_inv
  exact h_inv

/-- `phi_op_inv` 在 `Fin 256` 上是 injective。 -/
theorem phi_op_inv_injective : ∀ (x y : Fin 256), phi_op_inv x.val = phi_op_inv y.val → x = y := by
  intro x y h
  apply Fin.ext
  have hx := phi_op_inv_inverse_bounded x.val x.is_lt
  have hy := phi_op_inv_inverse_bounded y.val y.is_lt
  have h_inv : phi (phi_op_inv x.val) = phi (phi_op_inv y.val) := by rw [h]
  rw [hx, hy] at h_inv
  exact h_inv

/-- 完整解码管线：`decode_full = phi_op_inv ∘ decode_i41`。
    对应 Rust 的 `phi_op_inv[v_t]`。 -/
def decode_full (c0_eff c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) : Nat :=
  phi_op_inv (decode_i41 c0_eff c1_t c2 σ DDM q_sigma q_ddm)

/-- 完整 roundtrip：`decode_full(bridge(encode(phi(op)))) = op` 对 `op < 256`。
    即在 Rust 中 `phi_op_inv[decode(bridge(encode(phi(op))))] = original_op`。 -/
theorem full_bridge_decode_invariant (op anchor c1_t c2 σ DDM : Nat)
    (q_sigma q_ddm : QAvalancheConfig) (hop : op < 256) :
    decode_full (bridge_i41 (encode_c0_i41 (phi op) anchor c2 q_sigma q_ddm)
                 anchor c1_t c2 σ DDM q_sigma q_ddm)
                c1_t c2 σ DDM q_sigma q_ddm = op := by
  unfold decode_full
  have h := bridge_decode_invariant (phi op) anchor c1_t c2 σ DDM q_sigma q_ddm
  rw [h]
  rw [phi_inverse op, Nat.mod_eq_of_lt hop]

/-- `decode_full` 在任意状态下均产生有界值（`< 256`）。 -/
theorem decode_full_lt_256 (c0_eff c1_t c2 σ DDM : Nat)
    (q_sigma q_ddm : QAvalancheConfig) : decode_full c0_eff c1_t c2 σ DDM q_sigma q_ddm < 256 :=
  phi_op_inv_lt_256 _
