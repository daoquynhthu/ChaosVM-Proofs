import ChaosvmProofs.Definitions.Init

/-- T13: init_poisoned with non-zero poison diverges from clean init.
    Full proof in Definitions/Init.lean. -/
theorem T13_init_poisoned_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0) :
    init_poisoned k0 k1 r0 r1 pσ pC pD ≠ init k0 k1 r0 r1 :=
  init_poisoned_diverges k0 k1 r0 r1 pσ pC pD hp
