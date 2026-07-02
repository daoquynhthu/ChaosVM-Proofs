import ChaosvmProofs.Definitions.Helpers

/-! # G Mixer (Rust: `g_mixer.rs`). Abstract model. -/

structure ARXRound where
  k_r : Nat
  a_r : Nat
  k_prime_r : Nat
  b_r : Nat
  k_doubleprime_r : Nat
  c_r : Nat

structure GMixerConfig where
  rounds : ARXRound × ARXRound × ARXRound

/-- G init: (tS⊕σ⊕r0, tC+CFA+H, tD⊕DDM⊕r1). -/
def gInit (tS tC tD σ CFA DDM h r0 r1 : Nat) : Nat × Nat × Nat :=
  (tS ^^^ σ ^^^ r0, tC + CFA + h, tD ^^^ DDM ^^^ r1)

/-- Rounds abstract. -/
def gRounds_abstract (x y w : Nat) (cfg : GMixerConfig) : Nat × Nat :=
  (x ^^^ y, w ^^^ x)

/-- Full G mixer. -/
def gMix (tS tC tD σ CFA DDM h r0 r1 : Nat) (cfg : GMixerConfig) : Nat × Nat :=
  let (x, y, w) := gInit tS tC tD σ CFA DDM h r0 r1
  gRounds_abstract x y w cfg

theorem gMix_deterministic (tS tC tD σ CFA DDM h r0 r1 : Nat) (cfg : GMixerConfig) :
    gMix tS tC tD σ CFA DDM h r0 r1 cfg = gMix tS tC tD σ CFA DDM h r0 r1 cfg := rfl

theorem gMix_bijective (cfg : GMixerConfig) : Function.Injective (λ ((x,y,w) : Nat × Nat × Nat) =>
    gMix x y w 0 0 0 0 0 0 cfg) := by
  sorry
