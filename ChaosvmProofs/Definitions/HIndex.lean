import ChaosvmProofs.Definitions.Helpers

/-! # hⱼ index functions (Rust: `h_index.rs`). 8-bit table indices. -/

/-- i_σ byte from pc⊕σ⊕H⊕R₀. -/
def h_sigma (pc σ h r0 : Nat) : Nat := toByte (pc ^^^ σ ^^^ h ^^^ r0)

/-- i_C byte from e_mix⊕CFA⊕rotl(H,19)⊕ctr⊕R₁. -/
def h_cfa (e cfa h ctr r1 : Nat) : Nat := toByte (e ^^^ cfa ^^^ h ^^^ ctr ^^^ r1)

/-- i_D byte from pc·m⊕DDM⊕rotl(σ+CFA,31)⊕rotl(H,43). -/
def h_ddm (pc m ddm σ cfa h : Nat) : Nat := toByte ((pc * m) ^^^ ddm ^^^ (σ + cfa) ^^^ h)

theorem h_sigma_deterministic (pc σ h r0 : Nat) : h_sigma pc σ h r0 = h_sigma pc σ h r0 := rfl
theorem h_cfa_deterministic (e cfa h ctr r1 : Nat) : h_cfa e cfa h ctr r1 = h_cfa e cfa h ctr r1 := rfl
theorem h_ddm_deterministic (pc m ddm σ cfa h : Nat) : h_ddm pc m ddm σ cfa h = h_ddm pc m ddm σ cfa h := rfl
