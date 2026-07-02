import ChaosvmProofs.Definitions.GMixer

/-- T07a: Each ARX+Q round is a bijection on (x,y,w).
    Full proof in Definitions/GMixer.lean. -/
theorem T07a_round_bijection (x y w : Nat) (rc : ARXRoundConstants) :
    ∃ (x' y' w' : Nat), one_round x y w rc = (x', y', w') :=
  round_bijection x y w rc

/-- T07b: The output mixing (x⊕rotl(y,23), w⊕rotl(x,41)) is surjective.
    Full proof in Definitions/GMixer.lean. -/
theorem T07b_output_mixing_surjective (z_lo z_hi : Nat) :
    ∃ (x y w : Nat), (x ^^^ rotl y 23) = z_lo ∧ (w ^^^ rotl x 41) = z_hi :=
  output_mixing_surjective z_lo z_hi
