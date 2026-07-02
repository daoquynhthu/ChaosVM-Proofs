import ChaosvmProofs.Definitions.Helpers

/-! # ZFields: z_t bit decomposition (Rust: `z_layout.rs`). -/

structure ZFields where
  op_perm       : Nat
  handler_perm  : Nat
  sem_decomp    : Nat
  ctrl_edge_perm : Nat
  b_rd          : Nat
  b_ra          : Nat
  b_rb          : Nat
  branch_slot   : Nat
  a_rd          : Nat
  a_ra          : Nat
  a_rb          : Nat
  table_bank    : Nat
  spawn_trigger : Nat
  spawn_layout  : Nat
  state_salt_token : Nat

/-- Decompose (z_lo, z_hi) into ZFields. -/
def decompose (z_lo z_hi : Nat) : ZFields :=
  { op_perm := z_lo % 256,
    handler_perm := (z_lo / 256) % 256,
    sem_decomp := (z_lo / 65536) % 256,
    ctrl_edge_perm := (z_lo / 16777216) % 256,
    b_rd := (z_lo / 4294967296) % 256,
    b_ra := (z_lo / 1099511627776) % 256,
    b_rb := (z_lo / 281474976710656) % 256,
    branch_slot := (z_lo / 72057594037927936) % 256,
    a_rd := z_hi % 256,
    a_ra := (z_hi / 256) % 256,
    a_rb := (z_hi / 65536) % 256,
    table_bank := (z_hi / 16777216) % 256,
    spawn_trigger := (z_hi / 4294967296) % 256,
    spawn_layout := (z_hi / 1099511627776) % 256,
    state_salt_token := (z_hi / 281474976710656) % 65536 }

/-- Ensure affine multiplier is odd. -/
def ensure_odd (a : Nat) : Nat :=
  if a % 2 = 1 then a else a + 1

/-- Decompose with safe multipliers. -/
def decompose_safe (z_lo z_hi : Nat) : ZFields :=
  let f := decompose z_lo z_hi
  { f with a_rd := ensure_odd f.a_rd, a_ra := ensure_odd f.a_ra, a_rb := ensure_odd f.a_rb }

theorem ensure_odd_is_odd (a : Nat) : (ensure_odd a) % 2 = 1 := by
  unfold ensure_odd
  by_cases h : a % 2 = 1
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    have ha0 : a % 2 = 0 := by
      have hcases := Nat.mod_two_eq_zero_or_one a
      rcases hcases with (h0 | h1)
      · exact h0
      · exfalso; exact h h1
    simp [Nat.add_mod, ha0]

theorem decompose_safe_multipliers_odd (z_lo z_hi : Nat) :
    (decompose_safe z_lo z_hi).a_rd % 2 = 1 ∧
    (decompose_safe z_lo z_hi).a_ra % 2 = 1 ∧
    (decompose_safe z_lo z_hi).a_rb % 2 = 1 := by
  unfold decompose_safe
  simp [ensure_odd_is_odd]
