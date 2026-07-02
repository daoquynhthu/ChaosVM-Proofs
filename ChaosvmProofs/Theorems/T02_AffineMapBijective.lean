import ChaosvmProofs.Definitions.Permutation

/-- T02: affine_map(r,a,b) is bijective on ℤ₂₅₆ when a is odd.
    Identical to P_mod; proof reuses T01. -/
theorem T02_affine_map_bijective (a b : Nat) (ha_odd : a % 2 = 1) :
    Function.Injective (λ (r : Fin 256) => ((a * r.val + b) % 256 : Nat)) ∧
    (∀ (y : Fin 256), ∃ (r : Fin 256), ((a * r.val + b) % 256 : Nat) = y.val) :=
  P_mod_bijective a b ha_odd
