import ChaosvmProofs.Definitions.Helpers
import ChaosvmProofs.Definitions.QAvalanche

/-! # R_run initialization (Rust: `init.rs`). Now matches Rust faithfully. -/

structure InitState where
  sigma0       : Nat
  cfa0         : Nat
  ddm0         : Nat
  h0           : Nat
  poison_sigma : Nat
  poison_cfa   : Nat
  poison_ddm   : Nat

/-- Clean init: σ₀ = Q_σ(k0⊕r0⊕C_σ)⊕r1, etc. -/
def init (k0 k1 r0 r1 : Nat) (qσ qC qD qH : QAvalancheConfig) : InitState :=
  { sigma0 := qAvalanche (k0 ^^^ r0 ^^^ 0x1111111111111111) qσ ^^^ r1,
    cfa0 := qAvalanche (k1 ^^^ r1 ^^^ 0x2222222222222222) qC ^^^ r0,
    ddm0 := qAvalanche (k0 ^^^ r0 ^^^ 0x3333333333333333) qD ^^^ r1,
    h0 := qAvalanche (k1 ^^^ r1 ^^^ 0x4444444444444444) qH ^^^ r0,
    poison_sigma := 0,
    poison_cfa := 0,
    poison_ddm := 0 }

/-- Poisoned init: P ≠ 0 → diverges from clean.
    poison_seed = (pσ<<56) | (pC<<48) | (pD<<40). -/
def init_poisoned (k0 k1 r0 r1 pσ pC pD : Nat)
    (qσ qC qD qH : QAvalancheConfig) : InitState :=
  let clean := init k0 k1 r0 r1 qσ qC qD qH
  if pσ = 0 ∧ pC = 0 ∧ pD = 0 then clean
  else
    let poison_seed := Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40))
    { clean with
      sigma0 := clean.sigma0 ^^^ qAvalanche (poison_seed ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ,
      cfa0 := clean.cfa0 ^^^ qAvalanche (poison_seed ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC,
      ddm0 := clean.ddm0 ^^^ qAvalanche (poison_seed ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD,
      h0 := clean.h0 ^^^ qAvalanche (poison_seed ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH,
      poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }

theorem init_deterministic (k0 k1 r0 r1 : Nat) (qσ qC qD qH : QAvalancheConfig) :
    init k0 k1 r0 r1 qσ qC qD qH = init k0 k1 r0 r1 qσ qC qD qH := rfl

theorem init_poisoned_zero_equals_clean (k0 k1 r0 r1 : Nat) (qσ qC qD qH : QAvalancheConfig) :
    init_poisoned k0 k1 r0 r1 0 0 0 qσ qC qD qH = init k0 k1 r0 r1 qσ qC qD qH := by
  unfold init_poisoned
  simp

theorem init_poisoned_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0) :
    init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH ≠ init k0 k1 r0 r1 qσ qC qD qH := by
  unfold init_poisoned
  have h_not_zero : ¬ (pσ = 0 ∧ pC = 0 ∧ pD = 0) := by
    intro ⟨hσ, hC, hD⟩
    rcases hp with (hpσ | hpC | hpD)
    · exact hpσ hσ
    · exact hpC hC
    · exact hpD hD
  rw [if_neg h_not_zero]
  intro h_eq
  rcases hp with (hpσ | hpC | hpD)
  · -- pσ ≠ 0 → poison_sigma differs
    have h_ps : (let clean := init k0 k1 r0 r1 qσ qC qD qH; { clean with
        sigma0 := clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ,
        cfa0 := clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC,
        ddm0 := clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD,
        h0 := clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH,
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_sigma = pσ := rfl
    have h_clean_ps : (init k0 k1 r0 r1 qσ qC qD qH).poison_sigma = 0 := rfl
    have h_ps_eq : (let clean := init k0 k1 r0 r1 qσ qC qD qH; { clean with
        sigma0 := clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ,
        cfa0 := clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC,
        ddm0 := clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD,
        h0 := clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH,
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_sigma = (init k0 k1 r0 r1 qσ qC qD qH).poison_sigma := by rw [h_eq]
    rw [h_ps, h_clean_ps] at h_ps_eq
    exact hpσ h_ps_eq
  · -- pC ≠ 0 → poison_cfa differs
    have h_pc : (let clean := init k0 k1 r0 r1 qσ qC qD qH; { clean with
        sigma0 := clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ,
        cfa0 := clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC,
        ddm0 := clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD,
        h0 := clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH,
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_cfa = pC := rfl
    have h_clean_pc : (init k0 k1 r0 r1 qσ qC qD qH).poison_cfa = 0 := rfl
    have h_pc_eq : (let clean := init k0 k1 r0 r1 qσ qC qD qH; { clean with
        sigma0 := clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ,
        cfa0 := clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC,
        ddm0 := clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD,
        h0 := clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH,
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_cfa = (init k0 k1 r0 r1 qσ qC qD qH).poison_cfa := by rw [h_eq]
    rw [h_pc, h_clean_pc] at h_pc_eq
    exact hpC h_pc_eq
  · -- pD ≠ 0 → poison_ddm differs
    have h_pd : (let clean := init k0 k1 r0 r1 qσ qC qD qH; { clean with
        sigma0 := clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ,
        cfa0 := clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC,
        ddm0 := clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD,
        h0 := clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH,
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_ddm = pD := rfl
    have h_clean_pd : (init k0 k1 r0 r1 qσ qC qD qH).poison_ddm = 0 := rfl
    have h_pd_eq : (let clean := init k0 k1 r0 r1 qσ qC qD qH; { clean with
        sigma0 := clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ,
        cfa0 := clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC,
        ddm0 := clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD,
        h0 := clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH,
        poison_sigma := pσ, poison_cfa := pC, poison_ddm := pD }).poison_ddm = (init k0 k1 r0 r1 qσ qC qD qH).poison_ddm := by rw [h_eq]
    rw [h_pd, h_clean_pd] at h_pd_eq
    exact hpD h_pd_eq
