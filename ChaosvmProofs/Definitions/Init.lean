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

/-- Structural divergence: poison metadata fields (poison_sigma/cfa/ddm) differ.
    This proves struct inequality but NOT state-value divergence (sigma0/cfa0/ddm0/h0 may
    theoretically cancel via XOR). See `init_poisoned_sigma0_diverges` etc. for conditional
    state-value divergence. -/
theorem init_poisoned_structurally_differs (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
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

theorem xor_cancel_right (a x : Nat) : x = (a ^^^ x) ^^^ a := by
  calc
    x = x ^^^ 0 := by simp
    _ = x ^^^ (a ^^^ a) := by simp
    _ = (x ^^^ a) ^^^ a := by rw [Nat.xor_assoc]
    _ = (a ^^^ x) ^^^ a := by rw [Nat.xor_comm x a]

/-- XOR cancellation: `a ^^^ b ≠ 0 ↔ a ≠ b`。 -/
theorem xor_ne_zero_iff {a b : Nat} : a ^^^ b ≠ 0 ↔ a ≠ b := by
  constructor
  · intro h h_eq; subst h_eq; exact h (Nat.xor_self a)
  · intro h h_eq
    have h1 : (a ^^^ b) ^^^ b = (0 : Nat) ^^^ b := by rw [h_eq]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
    exact h (Nat.xor_zero a ▸ h1)

private theorem lor_testBit (a b i : Nat) : (a.lor b).testBit i = (a.testBit i || b.testBit i) := by
  unfold Nat.lor
  exact Nat.testBit_bitwise rfl a b i

private theorem lor_eq_zero_imp_left {a b : Nat} (h : a.lor b = 0) : a = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : (a.lor b).testBit i = (0 : Nat).testBit i := congrArg (·.testBit i) h
  rw [lor_testBit] at h1
  have h_zero : (0 : Nat).testBit i = false := by simp [Nat.testBit]
  rw [h_zero] at h1
  have h_ab := (Bool.or_eq_false_iff.mp h1).1
  exact h_ab.trans h_zero.symm

private theorem lor_eq_zero_imp_right {a b : Nat} (h : a.lor b = 0) : b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : (a.lor b).testBit i = (0 : Nat).testBit i := congrArg (·.testBit i) h
  rw [lor_testBit] at h1
  have h_zero : (0 : Nat).testBit i = false := by simp [Nat.testBit]
  rw [h_zero] at h1
  have h_ab := (Bool.or_eq_false_iff.mp h1).2
  exact h_ab.trans h_zero.symm

/-- poison_seed = (pσ<<56) | (pC<<48) | (pD<<40) 非零：任一分量非零则整体非零。
    使用 testBit 位运算性质：lor a b = 0 → a = 0 ∧ b = 0；shl x n = 0 → x = 0。 -/
theorem poison_seed_nonzero (pσ pC pD : Nat) (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0) :
    Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ≠ 0 := by
  intro h_eq
  have h1 : shl pσ 56 = 0 := lor_eq_zero_imp_left h_eq
  have h2 : Nat.lor (shl pC 48) (shl pD 40) = 0 := lor_eq_zero_imp_right h_eq
  have h3 : shl pC 48 = 0 := lor_eq_zero_imp_left h2
  have h4 : shl pD 40 = 0 := lor_eq_zero_imp_right h2
  unfold shl at h1 h3 h4
  rcases hp with (hpσ | hpC | hpD)
  · exact hpσ (by omega)
  · exact hpC (by omega)
  · exact hpD (by omega)

/-- T13b lemma: sigma0 diverges if qAvalanche of the σ poison seed ≠ 0. -/
theorem init_poisoned_sigma0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).sigma0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).sigma0 := by
  let clean := init k0 k1 r0 r1 qσ qC qD qH
  unfold init_poisoned
  have h_not_zero : ¬ (pσ = 0 ∧ pC = 0 ∧ pD = 0) := by
    intro hz; rcases hz with ⟨hσ, hC, hD⟩
    rcases hp with (hσ' | hC' | hD')
    · exact hσ' hσ
    · exact hC' hC
    · exact hD' hD
  rw [if_neg h_not_zero]
  intro h_eq; simp at h_eq
  have h_eq_clean : clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ = clean.sigma0 := by
    simpa [clean] using h_eq
  have h_av_zero : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ = 0 := by
    calc
      qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ
          = ((clean.sigma0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ) ^^^ clean.sigma0) :=
        xor_cancel_right clean.sigma0 (qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ)
      _ = clean.sigma0 ^^^ clean.sigma0 := by rw [h_eq_clean]
      _ = 0 := Nat.xor_self _
  exact h h_av_zero

/-- T13c lemma: cfa0 diverges if qAvalanche of the CFA poison seed ≠ 0. -/
theorem init_poisoned_cfa0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).cfa0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).cfa0 := by
  let clean := init k0 k1 r0 r1 qσ qC qD qH
  unfold init_poisoned
  have h_not_zero : ¬ (pσ = 0 ∧ pC = 0 ∧ pD = 0) := by
    intro hz; rcases hz with ⟨hσ, hC, hD⟩
    rcases hp with (hσ' | hC' | hD')
    · exact hσ' hσ
    · exact hC' hC
    · exact hD' hD
  rw [if_neg h_not_zero]
  intro h_eq; simp at h_eq
  have h_eq_clean : clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC = clean.cfa0 := by
    simpa [clean] using h_eq
  have h_av_zero : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC = 0 := by
    calc
      qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC
          = ((clean.cfa0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC) ^^^ clean.cfa0) :=
        xor_cancel_right clean.cfa0 (qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC)
      _ = clean.cfa0 ^^^ clean.cfa0 := by rw [h_eq_clean]
      _ = 0 := Nat.xor_self _
  exact h h_av_zero

/-- T13d lemma: ddm0 diverges if qAvalanche of the DDM poison seed ≠ 0. -/
theorem init_poisoned_ddm0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).ddm0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).ddm0 := by
  let clean := init k0 k1 r0 r1 qσ qC qD qH
  unfold init_poisoned
  have h_not_zero : ¬ (pσ = 0 ∧ pC = 0 ∧ pD = 0) := by
    intro hz; rcases hz with ⟨hσ, hC, hD⟩
    rcases hp with (hσ' | hC' | hD')
    · exact hσ' hσ
    · exact hC' hC
    · exact hD' hD
  rw [if_neg h_not_zero]
  intro h_eq; simp at h_eq
  have h_eq_clean : clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD = clean.ddm0 := by
    simpa [clean] using h_eq
  have h_av_zero : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD = 0 := by
    calc
      qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD
          = ((clean.ddm0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD) ^^^ clean.ddm0) :=
        xor_cancel_right clean.ddm0 (qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD)
      _ = clean.ddm0 ^^^ clean.ddm0 := by rw [h_eq_clean]
      _ = 0 := Nat.xor_self _
  exact h h_av_zero

/-- T13e lemma: h0 diverges if qAvalanche of the H poison seed ≠ 0. -/
theorem init_poisoned_h0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).h0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).h0 := by
  let clean := init k0 k1 r0 r1 qσ qC qD qH
  unfold init_poisoned
  have h_not_zero : ¬ (pσ = 0 ∧ pC = 0 ∧ pD = 0) := by
    intro hz; rcases hz with ⟨hσ, hC, hD⟩
    rcases hp with (hσ' | hC' | hD')
    · exact hσ' hσ
    · exact hC' hC
    · exact hD' hD
  rw [if_neg h_not_zero]
  intro h_eq; simp at h_eq
  have h_eq_clean : clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH = clean.h0 := by
    simpa [clean] using h_eq
  have h_av_zero : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH = 0 := by
    calc
      qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH
          = ((clean.h0 ^^^ qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH) ^^^ clean.h0) :=
        xor_cancel_right clean.h0 (qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH)
      _ = clean.h0 ^^^ clean.h0 := by rw [h_eq_clean]
      _ = 0 := Nat.xor_self _
  exact h h_av_zero
