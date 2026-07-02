import ChaosvmProofs.Definitions.Permutation

/-! # Semantic share encode/decode I-41 (Rust: `sem_share.rs`).

## Abstraction note

The definitions below use `P_mod anchor 1 0` / `P_mod c2 1 0` etc. where the Rust
implementation uses `permute(anchor, 0, q_sigma)` / `permute(c2, 0, q_ddm)`.

The formal model **abstracts away the QAvalanche parameters** (`q_sigma`, `q_ddm`):
- For `state = 0`, the models coincide: `q_avalanche(0, q) = 0` for any q, so
  `permute(val, 0, q) = (0|1)·val + 0 = val = P_mod val 1 0`.
- For `state ≠ 0`, Lean's `P_mod c1_t 1 σ = (c1_t + σ) % 256` differs from
  Rust's `permute(c1_t, σ, q_sigma) = a·c1_t + b` (where `(a,b)` derive from
  `q_avalanche(σ, q_sigma)`). The algebraic cancellation holds for **any** `P(k,s)`,
  because each P-term appears exactly twice and cancels by XOR self-cancellation.
-/

/-- c0 = u ⊕ P(anchor,0) ⊕ P(c2,0). -/
def encode_c0_i41 (u anchor c2 : Nat) : Nat :=
  u ^^^ (P_mod anchor 1 0) ^^^ (P_mod c2 1 0)

/-- J_t bridge. -/
def bridge_i41 (c0 anchor c1_t c2 σ DDM : Nat) : Nat :=
  c0 ^^^ (P_mod c1_t 1 σ) ^^^ (P_mod anchor 1 0) ^^^ (P_mod c2 1 DDM) ^^^ (P_mod c2 1 0)

/-- Decode: v = c0_eff ⊕ P(c1,σ) ⊕ P(c2,DDM). -/
def decode_i41 (c0_eff c1_t c2 σ DDM : Nat) : Nat :=
  c0_eff ^^^ (P_mod c1_t 1 σ) ^^^ (P_mod c2 1 DDM)

/-- XOR swap: x ^^^ y ^^^ x = y. -/
theorem swap_pair (x y : Nat) : x ^^^ y ^^^ x = y := by
  calc
    x ^^^ y ^^^ x = x ^^^ (x ^^^ y) := by
      simp [Nat.xor_comm]
    _ = (x ^^^ x) ^^^ y := by rw [← Nat.xor_assoc]
    _ = 0 ^^^ y := by rw [Nat.xor_self]
    _ = y := by simp

/-- Core invariant: decode(bridge(encode(op))) = op ∀ σ,DDM,c1,anchor,c2. -/
theorem bridge_decode_invariant (u anchor c1_t c2 σ DDM : Nat) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2) anchor c1_t c2 σ DDM) c1_t c2 σ DDM = u := by
  unfold encode_c0_i41 bridge_i41 decode_i41
  let A := P_mod anchor 1 0
  let B := P_mod c2 1 0
  let C := P_mod c1_t 1 σ
  let D := P_mod c2 1 DDM
  have hA_cancel : u ^^^ A ^^^ B ^^^ C ^^^ A = u ^^^ B ^^^ C := by
    calc
      u ^^^ A ^^^ B ^^^ C ^^^ A = u ^^^ (A ^^^ B ^^^ C ^^^ A) := by
        simp [Nat.xor_assoc]
      _ = u ^^^ (A ^^^ (B ^^^ C) ^^^ A) := by
        simp [Nat.xor_assoc]
      _ = u ^^^ (B ^^^ C) := by rw [swap_pair A (B ^^^ C)]
      _ = u ^^^ B ^^^ C := by simp [Nat.xor_assoc]
  have hBC : B ^^^ C ^^^ B ^^^ C = 0 := by
    calc
      B ^^^ C ^^^ B ^^^ C = ((B ^^^ C) ^^^ B) ^^^ C := rfl
      _ = (B ^^^ C) ^^^ (B ^^^ C) := by rw [Nat.xor_assoc]
      _ = 0 := by rw [Nat.xor_self]
  have h_inner : D ^^^ B ^^^ C ^^^ D = B ^^^ C := by
    calc
      D ^^^ B ^^^ C ^^^ D = D ^^^ (B ^^^ C) ^^^ D := by simp [Nat.xor_assoc]
      _ = B ^^^ C := swap_pair D (B ^^^ C)
  have h_rest : (u ^^^ B ^^^ C) ^^^ D ^^^ B ^^^ C ^^^ D = u := by
    calc
      (u ^^^ B ^^^ C) ^^^ D ^^^ B ^^^ C ^^^ D
          = (u ^^^ B ^^^ C) ^^^ (D ^^^ B ^^^ C ^^^ D) := by
        simp [Nat.xor_assoc]
      _ = (u ^^^ B ^^^ C) ^^^ (B ^^^ C) := by rw [h_inner]
      _ = u ^^^ B ^^^ C ^^^ B ^^^ C := by rw [← Nat.xor_assoc]
      _ = u ^^^ (B ^^^ C ^^^ B ^^^ C) := by simp [Nat.xor_assoc]
      _ = u ^^^ 0 := by rw [hBC]
      _ = u := by simp
  calc
    u ^^^ A ^^^ B ^^^ C ^^^ A ^^^ D ^^^ B ^^^ C ^^^ D
        = (u ^^^ A ^^^ B ^^^ C ^^^ A) ^^^ D ^^^ B ^^^ C ^^^ D := by
      simp [Nat.xor_assoc]
    _ = (u ^^^ B ^^^ C) ^^^ D ^^^ B ^^^ C ^^^ D := by rw [hA_cancel]
    _ = u := by rw [h_rest]
