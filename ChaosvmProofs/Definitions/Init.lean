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
  have h_not_zero : ¬ (pσ = 0 ∧ pC = 0 ∧ pD = 0) := by
    intro ⟨hσ, hC, hD⟩
    rcases hp with (hpσ | hpC | hpD)
    · exact hpσ hσ
    · exact hpC hC
    · exact hpD hD
  rw [if_neg h_not_zero]
  intro h_eq
  have h_clean_poison_sigma : (init k0 k1 r0 r1).poison_sigma = 0 := rfl
  have h_clean_poison_cfa : (init k0 k1 r0 r1).poison_cfa = 0 := rfl
  have h_clean_poison_ddm : (init k0 k1 r0 r1).poison_ddm = 0 := rfl
  rcases hp with (hpσ | hpC | hpD)
  · -- pσ ≠ 0 → poison_sigma differs
    have h_ps : (let clean := init k0 k1 r0 r1; { clean with
        sigma0 := clean.sigma0 ^^^ (pσ ^^^ r0 ^^^ r1),
        cfa0 := clean.cfa0 ^^^ (pC ^^^ r0 ^^^ r1),
        ddm0 := clean.ddm0 ^^^ (pD ^^^ r0 ^^^ r1),
        h0 := clean.h0 ^^^ ((pσ + pC + pD) ^^^ r0 ^^^ r1),
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_sigma = pσ := rfl
    have h_clean_ps : (init k0 k1 r0 r1).poison_sigma = 0 := rfl
    have h_ps_eq : (let clean := init k0 k1 r0 r1; { clean with
        sigma0 := clean.sigma0 ^^^ (pσ ^^^ r0 ^^^ r1),
        cfa0 := clean.cfa0 ^^^ (pC ^^^ r0 ^^^ r1),
        ddm0 := clean.ddm0 ^^^ (pD ^^^ r0 ^^^ r1),
        h0 := clean.h0 ^^^ ((pσ + pC + pD) ^^^ r0 ^^^ r1),
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_sigma = (init k0 k1 r0 r1).poison_sigma := by rw [h_eq]
    rw [h_ps, h_clean_ps] at h_ps_eq
    exact hpσ h_ps_eq
  · -- pC ≠ 0 → poison_cfa differs
    have h_pc : (let clean := init k0 k1 r0 r1; { clean with
        sigma0 := clean.sigma0 ^^^ (pσ ^^^ r0 ^^^ r1),
        cfa0 := clean.cfa0 ^^^ (pC ^^^ r0 ^^^ r1),
        ddm0 := clean.ddm0 ^^^ (pD ^^^ r0 ^^^ r1),
        h0 := clean.h0 ^^^ ((pσ + pC + pD) ^^^ r0 ^^^ r1),
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_cfa = pC := rfl
    have h_clean_pc : (init k0 k1 r0 r1).poison_cfa = 0 := rfl
    have h_pc_eq : (let clean := init k0 k1 r0 r1; { clean with
        sigma0 := clean.sigma0 ^^^ (pσ ^^^ r0 ^^^ r1),
        cfa0 := clean.cfa0 ^^^ (pC ^^^ r0 ^^^ r1),
        ddm0 := clean.ddm0 ^^^ (pD ^^^ r0 ^^^ r1),
        h0 := clean.h0 ^^^ ((pσ + pC + pD) ^^^ r0 ^^^ r1),
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_cfa = (init k0 k1 r0 r1).poison_cfa := by rw [h_eq]
    rw [h_pc, h_clean_pc] at h_pc_eq
    exact hpC h_pc_eq
  · -- pD ≠ 0 → poison_ddm differs
    have h_pd : (let clean := init k0 k1 r0 r1; { clean with
        sigma0 := clean.sigma0 ^^^ (pσ ^^^ r0 ^^^ r1),
        cfa0 := clean.cfa0 ^^^ (pC ^^^ r0 ^^^ r1),
        ddm0 := clean.ddm0 ^^^ (pD ^^^ r0 ^^^ r1),
        h0 := clean.h0 ^^^ ((pσ + pC + pD) ^^^ r0 ^^^ r1),
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_ddm = pD := rfl
    have h_clean_pd : (init k0 k1 r0 r1).poison_ddm = 0 := rfl
    have h_pd_eq : (let clean := init k0 k1 r0 r1; { clean with
        sigma0 := clean.sigma0 ^^^ (pσ ^^^ r0 ^^^ r1),
        cfa0 := clean.cfa0 ^^^ (pC ^^^ r0 ^^^ r1),
        ddm0 := clean.ddm0 ^^^ (pD ^^^ r0 ^^^ r1),
        h0 := clean.h0 ^^^ ((pσ + pC + pD) ^^^ r0 ^^^ r1),
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_ddm = (init k0 k1 r0 r1).poison_ddm := by rw [h_eq]
    rw [h_pd, h_clean_pd] at h_pd_eq
    exact hpD h_pd_eq
