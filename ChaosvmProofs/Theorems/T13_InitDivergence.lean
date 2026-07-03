import ChaosvmProofs.Definitions.Init

/-- T13a: init_poisoned with non-zero poison is structurally different from clean init
    (poison metadata fields differ). For state-value divergence see T13b–T13e. -/
theorem T13_init_poisoned_structurally_differs (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0) :
    init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH ≠ init k0 k1 r0 r1 qσ qC qD qH :=
  init_poisoned_structurally_differs k0 k1 r0 r1 pσ pC pD qσ qC qD qH hp

/-- T13b: If qAvalanche of the sigma poison seed is non-zero, then sigma0 diverges. -/
theorem T13_sigma0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h_seed : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 13 ^^^ 0x9e3779b97f4a7c15) qσ ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).sigma0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).sigma0 :=
  init_poisoned_sigma0_diverges k0 k1 r0 r1 pσ pC pD qσ qC qD qH hp h_seed

/-- T13c: If qAvalanche of the cfa poison seed is non-zero, then cfa0 diverges. -/
theorem T13_cfa0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h_seed : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 23 ^^^ 0xbf58476d1ce4e5b9) qC ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).cfa0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).cfa0 :=
  init_poisoned_cfa0_diverges k0 k1 r0 r1 pσ pC pD qσ qC qD qH hp h_seed

/-- T13d: If qAvalanche of the ddm poison seed is non-zero, then ddm0 diverges. -/
theorem T13_ddm0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h_seed : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 31 ^^^ 0xda6b7f7c5e4d3a1b) qD ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).ddm0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).ddm0 :=
  init_poisoned_ddm0_diverges k0 k1 r0 r1 pσ pC pD qσ qC qD qH hp h_seed

/-- T13e: If qAvalanche of the h poison seed is non-zero, then h0 diverges. -/
theorem T13_h0_diverges (k0 k1 r0 r1 pσ pC pD : Nat) (qσ qC qD qH : QAvalancheConfig)
    (hp : pσ ≠ 0 ∨ pC ≠ 0 ∨ pD ≠ 0)
    (h_seed : qAvalanche (Nat.lor (shl pσ 56) (Nat.lor (shl pC 48) (shl pD 40)) ^^^ r0 ^^^ rotl r1 43 ^^^ 0xef4a3b2c1d0e9f8a) qH ≠ 0) :
    (init_poisoned k0 k1 r0 r1 pσ pC pD qσ qC qD qH).h0 ≠ (init k0 k1 r0 r1 qσ qC qD qH).h0 :=
  init_poisoned_h0_diverges k0 k1 r0 r1 pσ pC pD qσ qC qD qH hp h_seed
