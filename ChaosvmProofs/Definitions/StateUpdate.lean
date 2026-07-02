import ChaosvmProofs.Definitions.Helpers

/-! # State update (Rust: `state.rs`). Deterministic state machine. -/

structure NewState where
  h_next    : Nat
  d_sigma   : Nat
  d_cfa     : Nat
  d_ddm     : Nat
  sigma_next : Nat
  cfa_next   : Nat
  ddm_next   : Nat

/-- Hₜ₊₁ digest. -/
def digest_operands (ra_val rb_val : Nat) : Nat :=
  ra_val * 0x9e3779b97f4a7c15 + rb_val

/-- Hₜ₊₁ update. -/
def update_h (h ra_val rb_val result edge mem call spawn ent_mix : Nat) : Nat :=
  h ^^^ (digest_operands ra_val rb_val) ^^^ result ^^^ edge ^^^ mem ^^^ call ^^^ spawn ^^^ ent_mix

/-- Full state update (abstract; rotation abstracted). -/
def update_state (σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt : Nat) : NewState :=
  let h_next := update_h h ra_val rb_val result edge mem call spawn ent_mix
  let d_σ := h_next ^^^ z_hi ^^^ r0 ^^^ salt
  let d_C := h_next ^^^ (rotl z_lo 23) ^^^ edge ^^^ salt
  let d_D := h_next ^^^ (z_lo + z_hi) ^^^ ctr ^^^ salt
  { h_next := h_next,
    d_sigma := d_σ, d_cfa := d_C, d_ddm := d_D,
    sigma_next := (rotl (σ + d_σ) 17) ^^^ d_D,
    cfa_next := (rotl (CFA ^^^ d_C) 31) + d_σ,
    ddm_next := (rotl (DDM + d_D) 47) ^^^ d_C }

theorem update_state_deterministic (σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt : Nat) :
    update_state σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt =
    update_state σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt := rfl
