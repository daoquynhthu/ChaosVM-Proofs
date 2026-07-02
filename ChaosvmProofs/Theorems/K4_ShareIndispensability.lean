import ChaosvmProofs.Definitions.SemShare

/-! # K4: 三份额缺一不可 (Share Indispensability)

Each of the three semantic shares (c0, anchor, c2) is strictly necessary.
Zeroing any one share yields a wrong decode result.

## Theorems

- **K4a**: `decode(bridge(encode, anchor=0)) = u ⊕ P(anchor,0)` — equals `u` only if `anchor%256 = 0`
- **K4b**: `decode(bridge(encode, c2=0)) = u ⊕ P(c2,0) ⊕ P(0,DDM) ⊕ P(c2,DDM)` — equals `u` only if `P(c2,0) ⊕ P(0,DDM) ⊕ P(c2,DDM) = 0`
- **K4c**: `decode(bridge(c0=0)) = P(anchor,0) ⊕ P(c2,0)` — equals `u` only by coincidence
-/

set_option maxHeartbeats 50000000

namespace K4

theorem xor_left_cancel (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  calc
    b = (a ^^^ a) ^^^ b := by simp
    _ = a ^^^ (a ^^^ b) := by rw [Nat.xor_assoc]
    _ = a ^^^ (a ^^^ c) := by rw [h]
    _ = (a ^^^ a) ^^^ c := by rw [Nat.xor_assoc]
    _ = c := by simp

theorem xor_swap_first (a b x : Nat) : a ^^^ (b ^^^ x) = b ^^^ (a ^^^ x) := by
  calc
    a ^^^ (b ^^^ x) = (a ^^^ b) ^^^ x := by rw [Nat.xor_assoc]
    _ = (b ^^^ a) ^^^ x := by rw [Nat.xor_comm a b]
    _ = b ^^^ (a ^^^ x) := by rw [Nat.xor_assoc]

/-- K4a: Zeroing anchor in bridge gives `u ⊕ P(anchor,1,0)`. -/
theorem anchor_zeroed (u anchor c1_t c2 σ DDM : Nat) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2) 0 c1_t c2 σ DDM) c1_t c2 σ DDM = u ^^^ P_mod anchor 1 0 := by
  unfold encode_c0_i41 bridge_i41 decode_i41
  have hP0 : P_mod 0 1 0 = 0 := by unfold P_mod; simp
  rw [hP0, Nat.xor_zero]
  let A := P_mod anchor 1 0
  let B := P_mod c2 1 0
  let C := P_mod c1_t 1 σ
  let E := P_mod c2 1 DDM
  have h_inner : B ^^^ (C ^^^ (E ^^^ (B ^^^ (C ^^^ E)))) = 0 := by
    calc
      B ^^^ (C ^^^ (E ^^^ (B ^^^ (C ^^^ E)))) = C ^^^ (B ^^^ (E ^^^ (B ^^^ (C ^^^ E)))) := by
        rw [xor_swap_first B C (E ^^^ (B ^^^ (C ^^^ E)))]
      _ = C ^^^ (E ^^^ (B ^^^ (B ^^^ (C ^^^ E)))) := by
        rw [xor_swap_first B E (B ^^^ (C ^^^ E))]
      _ = C ^^^ (E ^^^ ((B ^^^ B) ^^^ (C ^^^ E))) := by rw [← Nat.xor_assoc B B (C ^^^ E)]
      _ = C ^^^ (E ^^^ (0 ^^^ (C ^^^ E))) := by rw [Nat.xor_self _]
      _ = C ^^^ (E ^^^ (C ^^^ E)) := by simp
      _ = (C ^^^ E) ^^^ (C ^^^ E) := by rw [← Nat.xor_assoc C E (C ^^^ E)]
      _ = 0 := Nat.xor_self _
      _ = C ^^^ C := by rw [Nat.xor_self _]
      _ = 0 := Nat.xor_self _
  repeat rw [Nat.xor_assoc]
  have h_main : A ^^^ (B ^^^ (C ^^^ (E ^^^ (B ^^^ (C ^^^ E))))) = A := by
    rw [h_inner, Nat.xor_zero]
  rw [h_main]

/-- Corollary: if `P_mod anchor 1 0 ≠ 0` (i.e. `anchor % 256 ≠ 0`), decode ≠ u. -/
theorem anchor_zeroed_ne_u (u anchor c1_t c2 σ DDM : Nat) (h : P_mod anchor 1 0 ≠ 0) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2) 0 c1_t c2 σ DDM) c1_t c2 σ DDM ≠ u := by
  rw [anchor_zeroed]
  intro h_eq
  apply h
  have h_u : u ^^^ P_mod anchor 1 0 = u ^^^ 0 := by
    calc
      u ^^^ P_mod anchor 1 0 = u := h_eq
      _ = u ^^^ 0 := by simp
  exact xor_left_cancel u (P_mod anchor 1 0) 0 h_u

/-- K4b: Zeroing c2 in bridge gives `u ⊕ P(c2,1,0) ⊕ P(0,1,DDM) ⊕ P(c2,1,DDM)`. -/
theorem c2_zeroed (u anchor c1_t c2 σ DDM : Nat) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2) anchor c1_t 0 σ DDM) c1_t c2 σ DDM =
    u ^^^ P_mod c2 1 0 ^^^ P_mod 0 1 DDM ^^^ P_mod c2 1 DDM := by
  unfold encode_c0_i41 bridge_i41 decode_i41
  have hE : P_mod 0 1 0 = 0 := by unfold P_mod; simp
  rw [hE, Nat.xor_zero]
  let A := P_mod anchor 1 0
  let B := P_mod c2 1 0
  let C := P_mod c1_t 1 σ
  let D := P_mod 0 1 DDM
  let F := P_mod c2 1 DDM
  have h_inner2 : A ^^^ (C ^^^ (A ^^^ (D ^^^ (C ^^^ F)))) = D ^^^ F := by
    calc
      A ^^^ (C ^^^ (A ^^^ (D ^^^ (C ^^^ F)))) = C ^^^ (A ^^^ (A ^^^ (D ^^^ (C ^^^ F)))) := by
        rw [xor_swap_first A C (A ^^^ (D ^^^ (C ^^^ F)))]
      _ = C ^^^ ((A ^^^ A) ^^^ (D ^^^ (C ^^^ F))) := by rw [← Nat.xor_assoc A A (D ^^^ (C ^^^ F))]
      _ = C ^^^ (0 ^^^ (D ^^^ (C ^^^ F))) := by rw [Nat.xor_self _]
      _ = C ^^^ (D ^^^ (C ^^^ F)) := by simp
      _ = C ^^^ (C ^^^ (D ^^^ F)) := by rw [xor_swap_first D C F]
      _ = (C ^^^ C) ^^^ (D ^^^ F) := by rw [Nat.xor_assoc]
      _ = 0 ^^^ (D ^^^ F) := by rw [Nat.xor_self _]
      _ = D ^^^ F := by simp
  repeat rw [Nat.xor_assoc]
  have h_main2 : A ^^^ (B ^^^ (C ^^^ (A ^^^ (D ^^^ (C ^^^ F))))) = B ^^^ (D ^^^ F) := by
    rw [xor_swap_first A B (C ^^^ (A ^^^ (D ^^^ (C ^^^ F))))]
    rw [h_inner2]
  rw [h_main2]

/-- K4c: Zeroing c0 in bridge gives `P(anchor,1,0) ⊕ P(c2,1,0)`. -/
theorem c0_zeroed (_u anchor c1_t c2 σ DDM : Nat) :
    decode_i41 (bridge_i41 0 anchor c1_t c2 σ DDM) c1_t c2 σ DDM = P_mod anchor 1 0 ^^^ P_mod c2 1 0 := by
  unfold bridge_i41 decode_i41
  simp
  let A := P_mod anchor 1 0
  let B := P_mod c2 1 0
  let C := P_mod c1_t 1 σ
  let D := P_mod c2 1 DDM
  have h_inner_c : C ^^^ (D ^^^ (B ^^^ (C ^^^ D))) = B := by
    calc
      C ^^^ (D ^^^ (B ^^^ (C ^^^ D))) = D ^^^ (C ^^^ (B ^^^ (C ^^^ D))) := by
        rw [xor_swap_first C D (B ^^^ (C ^^^ D))]
      _ = D ^^^ (B ^^^ (C ^^^ (C ^^^ D))) := by
        rw [xor_swap_first C B (C ^^^ D)]
      _ = D ^^^ (B ^^^ ((C ^^^ C) ^^^ D)) := by rw [← Nat.xor_assoc C C D]
      _ = D ^^^ (B ^^^ (0 ^^^ D)) := by rw [Nat.xor_self _]
      _ = D ^^^ (B ^^^ D) := by simp
      _ = (D ^^^ B) ^^^ D := by rw [Nat.xor_assoc]
      _ = B := by rw [swap_pair D B]
  repeat rw [Nat.xor_assoc]
  rw [xor_swap_first C A (D ^^^ (B ^^^ (C ^^^ D)))]
  rw [h_inner_c]

end K4
