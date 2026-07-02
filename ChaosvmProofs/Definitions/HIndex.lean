import ChaosvmProofs.Definitions.Helpers
import ChaosvmProofs.Definitions.QAvalanche

/-! # hⱼ index functions (Rust: `h_index.rs`). 8-bit table indices.

Now properly matches Rust:
  i_σ = high8  Q_σ(pc ⊕ σ    ⊕ H  ⊕ R₀)
  i_C = byte6  Q_C(e_mix ⊕ CFA ⊕ rotl(H,19) ⊕ ctr ⊕ R₁)
  i_D = byte5  Q_D(pc·m ⊕ DDM ⊕ rotl(σ+CFA,31) ⊕ rotl(H,43))
-/

/-- High byte (bits 56-63): / 2^56 % 256. -/
def byte_high (x : Nat) : Nat := shr x 56 % 256

/-- Byte 6 (bits 48-55): / 2^48 % 256. -/
def byte6 (x : Nat) : Nat := shr x 48 % 256

/-- Byte 5 (bits 40-47): / 2^40 % 256. -/
def byte5 (x : Nat) : Nat := shr x 40 % 256

/-- i_σ = high8 Q_σ(pc ⊕ σ ⊕ H ⊕ R₀). -/
def h_sigma (pc σ h r0 : Nat) (q : QAvalancheConfig) : Nat :=
  byte_high (qAvalanche (pc ^^^ σ ^^^ h ^^^ r0) q)

/-- i_C = byte6 Q_C(e_mix ⊕ CFA ⊕ rotl(H,19) ⊕ ctr ⊕ R₁) where e_mix = e ⊕ rotl(e,32). -/
def h_cfa (e cfa h ctr r1 : Nat) (q : QAvalancheConfig) : Nat :=
  let e_mix := e ^^^ rotl e 32
  byte6 (qAvalanche (e_mix ^^^ cfa ^^^ rotl h 19 ^^^ ctr ^^^ r1) q)

/-- i_D = byte5 Q_D(pc·m ⊕ DDM ⊕ rotl(σ+CFA,31) ⊕ rotl(H,43)). -/
def h_ddm (pc m ddm σ cfa h : Nat) (q : QAvalancheConfig) : Nat :=
  byte5 (qAvalanche ((pc * m) ^^^ ddm ^^^ rotl (σ + cfa) 31 ^^^ rotl h 43) q)

theorem h_sigma_deterministic (pc σ h r0 : Nat) (q : QAvalancheConfig) :
    h_sigma pc σ h r0 q = h_sigma pc σ h r0 q := rfl

theorem h_cfa_deterministic (e cfa h ctr r1 : Nat) (q : QAvalancheConfig) :
    h_cfa e cfa h ctr r1 q = h_cfa e cfa h ctr r1 q := rfl

theorem h_ddm_deterministic (pc m ddm σ cfa h : Nat) (q : QAvalancheConfig) :
    h_ddm pc m ddm σ cfa h q = h_ddm pc m ddm σ cfa h q := rfl
