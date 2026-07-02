import ChaosvmProofs.Definitions.Permutation

/-- T01: P_mod(a·x + b mod 256) is bijective on ℤ₂₅₆ when a is odd.
    Full proof in Definitions/Permutation.lean. -/
theorem T01_P_mod_bijective (a b : Nat) (ha_odd : a % 2 = 1) :
    Function.Injective (λ (x : Fin 256) => ((a * x.val + b) % 256 : Nat)) ∧
    (∀ (y : Fin 256), ∃ (x : Fin 256), ((a * x.val + b) % 256 : Nat) = y.val) :=
  P_mod_bijective a b ha_odd
