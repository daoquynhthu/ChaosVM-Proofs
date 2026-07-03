import ChaosvmProofs.Definitions.QAvalanche
import ChaosvmProofs.Definitions.StateUpdate
import ChaosvmProofs.Definitions.Step

set_option maxHeartbeats 50000000

open Nat

/-! # T14: Poison Cascade (H-chain injectivity)

If the H chain diverges (h₁ ≠ h₂) and the qAvalanche config for H
has an invertible multiplier (i.e. mult is odd, xor_shift ≥ 1), then
the divergence propagates through `update_h` when all other parameters
are identical.

This is the CORE of the poison-cascade property: the H-chain update is
injective in `h`.  T13 proves that init poisons produce different h₀.
`update_h_inj_in_h` guarantees they stay divergent through subsequent
H-chain updates.
-/

-- ── Helper: operand digest < 2^64 when rb_val < 2^64 ───────────────────

theorem digest_operands_lt_two_pow (ra_val rb_val : Nat) (hrb : rb_val < 2 ^ 64) :
    digest_operands ra_val rb_val < 2 ^ 64 := by
  unfold digest_operands
  have ha : (ra_val * 0x9e3779b97f4a7c15) % (2 ^ 64) < 2 ^ 64 :=
    Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hb : rotl rb_val 13 < 2 ^ 64 := rotl_lt_two_pow rb_val 13 hrb
  exact xor_lt_two_pow _ _ 64 ha hb

-- ── Helper: XOR with same key is injective ─────────────────────────────

theorem xor_inj (a b k : Nat) (h : a ^^^ k = b ^^^ k) : a = b := by
  calc
    a = (a ^^^ k) ^^^ k := by simp [Nat.xor_assoc]
    _ = (b ^^^ k) ^^^ k := by rw [h]
    _ = b := by simp [Nat.xor_assoc]

-- ── Core lemma: update_h is injective in h ──────────────────────────────
--
-- When all other parameters are identical, different h values produce
-- different update_h outputs.  This is the fundamental cascade property:
-- H-chain divergence is never lost.

theorem update_h_inj_in_h (h1 h2 ra_val rb_val result edge mem call spawn ent_mix : Nat)
    (q : QAvalancheConfig) (invMult : Nat) (h_diff : h1 ≠ h2)
    (h1_lt : h1 < 2 ^ 64) (h2_lt : h2 < 2 ^ 64)
    (hrb : rb_val < 2 ^ 64)
    (hres : result < 2 ^ 64)
    (h_edge : edge < 2 ^ 64) (h_mem : mem < 2 ^ 64)
    (h_call : call < 2 ^ 64) (h_spawn : spawn < 2 ^ 64)
    (h_ent : ent_mix < 2 ^ 64)
    (h_inv : (q.mult * invMult) % (2 ^ 64) = 1) (h_shift : 1 ≤ q.xor_shift) :
    update_h h1 ra_val rb_val result edge mem call spawn ent_mix q ≠
    update_h h2 ra_val rb_val result edge mem call spawn ent_mix q := by
  unfold update_h
  intro h_eq
  -- K_full = common XOR of all non-h components
  let K_full := digest_operands ra_val rb_val ^^^ rotl result 17 ^^^ edge ^^^ mem ^^^ call ^^^ spawn ^^^ ent_mix
  have hK_lt : K_full < 2 ^ 64 := by
    have hdig : digest_operands ra_val rb_val < 2 ^ 64 :=
      digest_operands_lt_two_pow ra_val rb_val hrb
    have hrot : rotl result 17 < 2 ^ 64 := rotl_lt_two_pow result 17 hres
    have h1' : (digest_operands ra_val rb_val ^^^ rotl result 17) < 2 ^ 64 :=
      xor_lt_two_pow _ _ 64 hdig hrot
    have h2' : (digest_operands ra_val rb_val ^^^ rotl result 17 ^^^ edge) < 2 ^ 64 :=
      xor_lt_two_pow _ _ 64 h1' h_edge
    have h3' : (digest_operands ra_val rb_val ^^^ rotl result 17 ^^^ edge ^^^ mem) < 2 ^ 64 :=
      xor_lt_two_pow _ _ 64 h2' h_mem
    have h4' : (digest_operands ra_val rb_val ^^^ rotl result 17 ^^^ edge ^^^ mem ^^^ call) < 2 ^ 64 :=
      xor_lt_two_pow _ _ 64 h3' h_call
    have h5' : (digest_operands ra_val rb_val ^^^ rotl result 17 ^^^ edge ^^^ mem ^^^ call ^^^ spawn) < 2 ^ 64 :=
      xor_lt_two_pow _ _ 64 h4' h_spawn
    have h6' : (digest_operands ra_val rb_val ^^^ rotl result 17 ^^^ edge ^^^ mem ^^^ call ^^^ spawn ^^^ ent_mix) < 2 ^ 64 :=
      xor_lt_two_pow _ _ 64 h5' h_ent
    exact h6'
  have h_input1_lt : (h1 ^^^ K_full) < 2 ^ 64 := xor_lt_two_pow _ _ 64 h1_lt hK_lt
  have h_input2_lt : (h2 ^^^ K_full) < 2 ^ 64 := xor_lt_two_pow _ _ 64 h2_lt hK_lt
  -- h_eq is about the inline form; rewrite to use K_full via associativity
  have h_qinputs_eq : qAvalanche (h1 ^^^ K_full) q = qAvalanche (h2 ^^^ K_full) q := by
    simpa [K_full, Nat.xor_assoc] using h_eq
  have h_xor_eq : h1 ^^^ K_full = h2 ^^^ K_full :=
    qAvalanche_inj (h1 ^^^ K_full) (h2 ^^^ K_full) q invMult h_qinputs_eq h_input1_lt h_input2_lt h_inv h_shift
  have h_h_eq : h1 = h2 := xor_inj h1 h2 K_full h_xor_eq
  exact h_diff h_h_eq

-- ── H-bound invariant: update_h always returns < 2^64 ───────────────────

theorem update_h_lt_two_pow (h ra_val rb_val result edge mem call spawn ent_mix : Nat)
    (q : QAvalancheConfig) : update_h h ra_val rb_val result edge mem call spawn ent_mix q < 2 ^ 64 := by
  unfold update_h
  exact qAvalanche_lt_two_pow _ _
