import ChaosvmProofs.Definitions.GMixer

/-- K1: The 3-round gRounds_internal is a bijection on (x,y,w) with a
    constructive left inverse (three one_round inverses, reversed order).

    Full proof in Definitions/GMixer.lean (gRounds_internal_inv_correct). -/
theorem K1_gRounds_bijection (x y w : Nat) (cfg : GMixerConfig) :
    gRounds_internal_inv (gRounds_internal x y w cfg) cfg = (x, y, w) :=
  gRounds_internal_inv_correct x y w cfg
