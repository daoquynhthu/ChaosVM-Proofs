import ChaosvmProofs.Definitions.GMixer

theorem T06_gRounds_deterministic (x y w : Nat) (cfg : GMixerConfig) :
    gRounds x y w cfg = gRounds x y w cfg := rfl
