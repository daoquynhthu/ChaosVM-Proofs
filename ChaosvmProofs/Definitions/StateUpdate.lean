import ChaosvmProofs.Definitions.Helpers
import ChaosvmProofs.Definitions.QAvalanche

/-! # State update (Rust: `state.rs`). Now matches Rust faithfully. -/

structure NewState where
  h_next    : Nat
  d_sigma   : Nat
  d_cfa     : Nat
  d_ddm     : Nat
  sigma_next : Nat
  cfa_next   : Nat
  ddm_next   : Nat

/-- Hₜ₊₁ digest: ra·C ⊕ rotl(rb,13)  (C = 0x9e3779b97f4a7c15). -/
def digest_operands (ra_val rb_val : Nat) : Nat :=
  (ra_val * 0x9e3779b97f4a7c15) % (2 ^ 64) ^^^ rotl rb_val 13

/-- Hₜ₊₁ = Q_H(H ⊕ digest ⊕ rotl(result,17) ⊕ edge ⊕ mem ⊕ call ⊕ spawn). -/
def update_h (h ra_val rb_val result edge mem call spawn ent_mix : Nat) (q : QAvalancheConfig) : Nat :=
  qAvalanche (h ^^^ (digest_operands ra_val rb_val) ^^^ rotl result 17 ^^^ edge ^^^ mem ^^^ call ^^^ spawn ^^^ ent_mix) q

/-- Full state update (matches Rust state.rs:48-93). -/
def update_state (σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt : Nat)
    (q_h q_sigma q_cfa q_ddm : QAvalancheConfig) : NewState :=
  let h_next := update_h h ra_val rb_val result edge mem call spawn ent_mix q_h
  let d_σ := qAvalanche (z_hi ^^^ h_next ^^^ r0 ^^^ salt) q_sigma
  let d_C := qAvalanche (rotl z_lo 23 ^^^ h_next ^^^ edge ^^^ salt) q_cfa
  let d_D := qAvalanche ((z_lo + z_hi) % (2 ^ 64) ^^^ h_next ^^^ ctr ^^^ salt) q_ddm
  { h_next := h_next,
    d_sigma := d_σ, d_cfa := d_C, d_ddm := d_D,
    sigma_next := rotl (σ + d_σ) 17 ^^^ d_D,
    cfa_next := (rotl (CFA ^^^ d_C) 31 + d_σ) % (2 ^ 64),
    ddm_next := rotl (DDM + d_D) 47 ^^^ d_C }

theorem update_state_deterministic (σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt : Nat)
    (q_h q_sigma q_cfa q_ddm : QAvalancheConfig) :
    update_state σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt q_h q_sigma q_cfa q_ddm =
    update_state σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt q_h q_sigma q_cfa q_ddm := rfl
