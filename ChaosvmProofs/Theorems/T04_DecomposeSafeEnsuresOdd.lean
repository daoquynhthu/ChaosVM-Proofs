import ChaosvmProofs.Definitions.ZLayout

/-- T04: decompose_safe ensures a_rd, a_ra, a_rb are odd.
    Proofs in Definitions/ZLayout.lean. -/
theorem T04_ensure_odd_is_odd (a : Nat) : (ensure_odd a) % 2 = 1 :=
  ensure_odd_is_odd a

theorem T04_decompose_safe_multipliers_odd (z_lo z_hi : Nat) :
    (decompose_safe z_lo z_hi).a_rd % 2 = 1 ∧
    (decompose_safe z_lo z_hi).a_ra % 2 = 1 ∧
    (decompose_safe z_lo z_hi).a_rb % 2 = 1 :=
  decompose_safe_multipliers_odd z_lo z_hi
