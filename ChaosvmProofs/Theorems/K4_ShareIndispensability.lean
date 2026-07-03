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

/-- K4a: Zeroing anchor in bridge gives `u ⊕ permute(anchor, 0, q_sigma)`. -/
theorem anchor_zeroed (u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2 q_sigma q_ddm) 0 c1_t c2 σ DDM q_sigma q_ddm)
               c1_t c2 σ DDM q_sigma q_ddm = u ^^^ permute anchor 0 q_sigma := by
  unfold encode_c0_i41 bridge_i41 decode_i41
  have hP0 : permute 0 0 q_sigma = 0 := by
    unfold permute
    have hqz : qAvalanche 0 q_sigma = 0 := qAvalanche_zero q_sigma
    simp [hqz, P_mod]
  rw [hP0, Nat.xor_zero]
  let A := permute anchor 0 q_sigma
  let B := permute c2 0 q_ddm
  let C := permute c1_t σ q_sigma
  let E := permute c2 DDM q_ddm
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

/-- Corollary: if `permute anchor 0 q_sigma ≠ 0` (i.e. `anchor % 256 ≠ 0`), decode ≠ u. -/
theorem anchor_zeroed_ne_u (u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) 
    (h : permute anchor 0 q_sigma ≠ 0) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2 q_sigma q_ddm) 0 c1_t c2 σ DDM q_sigma q_ddm)
               c1_t c2 σ DDM q_sigma q_ddm ≠ u := by
  rw [anchor_zeroed u anchor c1_t c2 σ DDM q_sigma q_ddm]
  intro h_eq
  apply h
  have h_u : u ^^^ permute anchor 0 q_sigma = u ^^^ 0 := by
    calc
      u ^^^ permute anchor 0 q_sigma = u := h_eq
      _ = u ^^^ 0 := by simp
  exact xor_left_cancel u (permute anchor 0 q_sigma) 0 h_u

/-- K4b: Zeroing c2 in bridge gives `u ⊕ permute(c2,0,q_ddm) ⊕ permute(0,DDM,q_ddm) ⊕ permute(c2,DDM,q_ddm)`. -/
theorem c2_zeroed (u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2 q_sigma q_ddm) anchor c1_t 0 σ DDM q_sigma q_ddm)
               c1_t c2 σ DDM q_sigma q_ddm =
    u ^^^ permute c2 0 q_ddm ^^^ permute 0 DDM q_ddm ^^^ permute c2 DDM q_ddm := by
  unfold encode_c0_i41 bridge_i41 decode_i41
  have hE : permute 0 0 q_ddm = 0 := by
    unfold permute
    have hqz : qAvalanche 0 q_ddm = 0 := qAvalanche_zero q_ddm
    simp [hqz, P_mod]
  rw [hE, Nat.xor_zero]
  let A := permute anchor 0 q_sigma
  let B := permute c2 0 q_ddm
  let C := permute c1_t σ q_sigma
  let D := permute 0 DDM q_ddm
  let F := permute c2 DDM q_ddm
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

/-- K4c: Zeroing c0 in bridge gives `permute(anchor,0,q_sigma) ⊕ permute(c2,0,q_ddm)`. -/
theorem c0_zeroed (_u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) :
    decode_i41 (bridge_i41 0 anchor c1_t c2 σ DDM q_sigma q_ddm) c1_t c2 σ DDM q_sigma q_ddm =
    permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm := by
  unfold bridge_i41 decode_i41
  simp
  let A := permute anchor 0 q_sigma
  let B := permute c2 0 q_ddm
  let C := permute c1_t σ q_sigma
  let D := permute c2 DDM q_ddm
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

/-- K4b 推论: `permute(c2,0) ⊕ permute(0,DDM) ⊕ permute(c2,DDM) ≠ 0` 时 decode ≠ u。 -/
theorem c2_zeroed_ne_u (u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig)
    (h : permute c2 0 q_ddm ^^^ permute 0 DDM q_ddm ^^^ permute c2 DDM q_ddm ≠ 0) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2 q_sigma q_ddm) anchor c1_t 0 σ DDM q_sigma q_ddm)
               c1_t c2 σ DDM q_sigma q_ddm ≠ u := by
  rw [c2_zeroed u anchor c1_t c2 σ DDM q_sigma q_ddm]
  intro h_eq
  apply h
  let X := permute c2 0 q_ddm ^^^ permute 0 DDM q_ddm ^^^ permute c2 DDM q_ddm
  have h_eq_X : u ^^^ X = u := by
    simpa [X, Nat.xor_assoc] using h_eq
  have hX : (u ^^^ X) ^^^ u = X := swap_pair u X
  calc
    X = (u ^^^ X) ^^^ u := hX.symm
    _ = u ^^^ u := by rw [h_eq_X]
    _ = 0 := Nat.xor_self _

/-- K4c 推论: `c0 ≠ 0` 时 decode ≠ u（即 c0 为零化时必须恢复原始编码才可能相等）。 -/
theorem c0_zeroed_ne_u (u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig)
    (h_c0 : (encode_c0_i41 u anchor c2 q_sigma q_ddm) ≠ 0) :
    decode_i41 (bridge_i41 0 anchor c1_t c2 σ DDM q_sigma q_ddm) c1_t c2 σ DDM q_sigma q_ddm ≠ u := by
  rw [c0_zeroed u anchor c1_t c2 σ DDM q_sigma q_ddm]
  intro h_eq
  apply h_c0
  unfold encode_c0_i41
  calc
    u ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm
        = u ^^^ (permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm) := by simp [Nat.xor_assoc]
    _ = (permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm) ^^^ (permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm) := by rw [h_eq]
    _ = 0 := by simp

end K4
