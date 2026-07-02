/-! # R_run initialization (Rust: `init.rs`). -/

structure InitState where
  sigma0       : Nat
  cfa0         : Nat
  ddm0         : Nat
  h0           : Nat
  poison_sigma : Nat
  poison_cfa   : Nat
  poison_ddm   : Nat

/-- Clean init (abstract). -/
def init (k0 k1 r0 r1 : Nat) : InitState :=
  { sigma0 := k0 ^^^ r0 ^^^ 0x1111111111111111,
    cfa0 := k1 ^^^ r1 ^^^ 0x2222222222222222,
    ddm0 := k0 ^^^ r0 ^^^ 0x3333333333333333,
    h0 := k1 ^^^ r1 ^^^ 0x4444444444444444,
    poison_sigma := 0,
    poison_cfa := 0,
    poison_ddm := 0 }

/-- Poisoned init: P ≠ 0 → diverges from clean. -/
def init_poisoned (k0 k1 r0 r1 pσ pC pD : Nat) : InitState :=
  let clean := init k0 k1 r0 r1
  if pσ = 0 ∧ pC = 0 ∧ pD = 0 then clean
  else { clean with
    sigma0 := clean.sigma0 ^^^ (pσ ^^^ r0 ^^^ r1),
    cfa0 := clean.cfa0 ^^^ (pC ^^^ r0 ^^^ r1),
    ddm0 := clean.ddm0 ^^^ (pD ^^^ r0 ^^^ r1),
    h0 := clean.h0 ^^^ ((pσ + pC + pD) ^^^ r0 ^^^ r1),
    poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }

theorem init_deterministic (k0 k1 r0 r1 : Nat) : init k0 k1 r0 r1 = init k0 k1 r0 r1 := rfl

theorem init_poisoned_zero_equals_clean (k0 k1 r0 r1 : Nat) : init_poisoned k0 k1 r0 r1 0 0 0 = init k0 k1 r0 r1 := by
  unfold init_poisoned
  simp

theorem init_poisoned_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0) :
    init_poisoned k0 k1 r0 r1 pσ pC pD ≠ init k0 k1 r0 r1 := by
  unfold init_poisoned
  sorry
