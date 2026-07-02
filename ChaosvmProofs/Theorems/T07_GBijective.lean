import ChaosvmProofs.Definitions.GMixer

/-- T07a: ARX+Q round has a constructive left inverse (→ injective).
    Full proof in Definitions/GMixer.lean. -/
theorem T07a_one_round_inv_correct (x y w : Nat) (rc : ARXRoundConstants)
    (q q_prime q_doubleprime : QAvalancheConfig) :
    one_round_inv (one_round x y w rc q q_prime q_doubleprime) rc q q_prime q_doubleprime = (x, y, w) :=
  one_round_inv_correct x y w rc q q_prime q_doubleprime

/-- T07b: The output mixing (x⊕rotl(y,23), w⊕rotl(x,41)) is surjective.
    Full proof in Definitions/GMixer.lean. -/
theorem T07b_output_mixing_surjective (z_lo z_hi : Nat) :
    ∃ (x y w : Nat), (x ^^^ rotl y 23) = z_lo ∧ (w ^^^ rotl x 41) = z_hi :=
  output_mixing_surjective z_lo z_hi
