import ChaosvmProofs.Definitions.Init
import ChaosvmProofs.Definitions.QAvalanche
import ChaosvmProofs.Definitions.StateUpdate
import ChaosvmProofs.Definitions.Step

set_option maxHeartbeats 50000000
set_option maxRecDepth 65536

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

-- ── P2a: 模加法单射（无需进位消除假设）─────────────────────────────────

theorem add_mod64_inj (a b k : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (a + k) % 2 ^ 64 = (b + k) % 2 ^ 64) : a = b := by
  omega

-- ── P2b: σ 链纵向级联 ──────────────────────────────────────────────
--
-- sigma_next = rotl(σ + d_σ, 17) ^^^ d_D
-- 要求 σ + d_σ < 2^64（保证 rotl64_inj 适用，即无 64 位溢出）

theorem sigma_next_inj_in_sigma (σ1 σ2 d_σ d_D : Nat) (h_diff : σ1 ≠ σ2)
    (hsum1 : σ1 + d_σ < 2 ^ 64) (hsum2 : σ2 + d_σ < 2 ^ 64) :
    rotl (σ1 + d_σ) 17 ^^^ d_D ≠ rotl (σ2 + d_σ) 17 ^^^ d_D := by
  intro h_eq
  have h_rotl_eq : rotl (σ1 + d_σ) 17 = rotl (σ2 + d_σ) 17 := xor_inj _ _ _ h_eq
  have h_sum_eq : σ1 + d_σ = σ2 + d_σ := by
    apply rotl64_inj (σ1 + d_σ) (σ2 + d_σ) 17
    · simpa [rotl] using h_rotl_eq
    · exact hsum1
    · exact hsum2
  omega

-- ── P2c: DDM 链纵向级联 ─────────────────────────────────────────────
--
-- ddm_next = rotl(DDM + d_D, 47) ^^^ d_C
-- 要求 DDM + d_D < 2^64

theorem ddm_next_inj_in_ddm (DDM1 DDM2 d_D d_C : Nat) (h_diff : DDM1 ≠ DDM2)
    (hsum1 : DDM1 + d_D < 2 ^ 64) (hsum2 : DDM2 + d_D < 2 ^ 64) :
    rotl (DDM1 + d_D) 47 ^^^ d_C ≠ rotl (DDM2 + d_D) 47 ^^^ d_C := by
  intro h_eq
  have h_rotl_eq : rotl (DDM1 + d_D) 47 = rotl (DDM2 + d_D) 47 := xor_inj _ _ _ h_eq
  have h_sum_eq : DDM1 + d_D = DDM2 + d_D := by
    apply rotl64_inj (DDM1 + d_D) (DDM2 + d_D) 47
    · simpa [rotl] using h_rotl_eq
    · exact hsum1
    · exact hsum2
  omega

-- ── P2d: CFA 链纵向级联 ─────────────────────────────────────────────
--
-- cfa_next = (rotl(CFA ^^^ d_C, 31) + d_σ) % 2^64
-- 不需要和 < 2^64 条件（CFA ^^^ d_C 自动 < 2^64 通过 xor_lt_two_pow 保证，
-- 模加法通过 add_mod64_inj 消除进位）

theorem cfa_next_inj_in_cfa (CFA1 CFA2 d_C d_σ : Nat) (h_diff : CFA1 ≠ CFA2)
    (hCFA1 : CFA1 < 2 ^ 64) (hCFA2 : CFA2 < 2 ^ 64) (hdC : d_C < 2 ^ 64) :
    (rotl (CFA1 ^^^ d_C) 31 + d_σ) % 2 ^ 64 ≠ (rotl (CFA2 ^^^ d_C) 31 + d_σ) % 2 ^ 64 := by
  intro h_eq
  have h_xor1_lt : CFA1 ^^^ d_C < 2 ^ 64 := xor_lt_two_pow _ _ 64 hCFA1 hdC
  have h_xor2_lt : CFA2 ^^^ d_C < 2 ^ 64 := xor_lt_two_pow _ _ 64 hCFA2 hdC
  have h_rotl1_lt : rotl (CFA1 ^^^ d_C) 31 < 2 ^ 64 := rotl_lt_two_pow _ _ h_xor1_lt
  have h_rotl2_lt : rotl (CFA2 ^^^ d_C) 31 < 2 ^ 64 := rotl_lt_two_pow _ _ h_xor2_lt
  have h_rotl_eq : rotl (CFA1 ^^^ d_C) 31 = rotl (CFA2 ^^^ d_C) 31 :=
    add_mod64_inj _ _ d_σ h_rotl1_lt h_rotl2_lt h_eq
  have h_xor_eq : CFA1 ^^^ d_C = CFA2 ^^^ d_C := by
    apply rotl64_inj (CFA1 ^^^ d_C) (CFA2 ^^^ d_C) 31
    · simpa [rotl] using h_rotl_eq
    · exact h_xor1_lt
    · exact h_xor2_lt
  have h_CFA_eq : CFA1 = CFA2 := xor_inj _ _ d_C h_xor_eq
  exact h_diff h_CFA_eq

-- ── P3a–c: δ 单射（d_σ/d_C/d_D 各使其 next 值不同）────────────────────
--
-- sigma_next = rotl(σ + d_σ, 17) ^^^ d_D 中 σ 和 d_σ 对称，重用 P2b
-- cfa_next   = (rotl(CFA ^^^ d_C, 31) + d_σ) % 2^64，d_C 对称于 CFA
-- ddm_next   = rotl(DDM + d_D, 47) ^^^ d_C，DDM 和 d_D 对称

theorem sigma_next_inj_in_d_sigma (σ d_σ1 d_σ2 d_D : Nat) (h_diff : d_σ1 ≠ d_σ2)
    (hsum1 : σ + d_σ1 < 2 ^ 64) (hsum2 : σ + d_σ2 < 2 ^ 64) :
    rotl (σ + d_σ1) 17 ^^^ d_D ≠ rotl (σ + d_σ2) 17 ^^^ d_D := by
  have h1' : d_σ1 + σ < 2 ^ 64 := (Nat.add_comm σ d_σ1).symm ▸ hsum1
  have h2' : d_σ2 + σ < 2 ^ 64 := (Nat.add_comm σ d_σ2).symm ▸ hsum2
  have h := sigma_next_inj_in_sigma d_σ1 d_σ2 σ d_D h_diff h1' h2'
  -- h : rotl (d_σ1 + σ) 17 ^^^ d_D ≠ rotl (d_σ2 + σ) 17 ^^^ d_D
  simpa [Nat.add_comm] using h

theorem ddm_next_inj_in_d_d (DDM d_D1 d_D2 d_C : Nat) (h_diff : d_D1 ≠ d_D2)
    (hsum1 : DDM + d_D1 < 2 ^ 64) (hsum2 : DDM + d_D2 < 2 ^ 64) :
    rotl (DDM + d_D1) 47 ^^^ d_C ≠ rotl (DDM + d_D2) 47 ^^^ d_C := by
  have h1' : d_D1 + DDM < 2 ^ 64 := (Nat.add_comm DDM d_D1).symm ▸ hsum1
  have h2' : d_D2 + DDM < 2 ^ 64 := (Nat.add_comm DDM d_D2).symm ▸ hsum2
  have h := ddm_next_inj_in_ddm d_D1 d_D2 DDM d_C h_diff h1' h2'
  simpa [Nat.add_comm] using h

theorem cfa_next_inj_in_d_c (CFA d_C1 d_C2 d_σ : Nat) (h_diff : d_C1 ≠ d_C2)
    (hCFA : CFA < 2 ^ 64) (hdC1 : d_C1 < 2 ^ 64) (hdC2 : d_C2 < 2 ^ 64) :
    (rotl (CFA ^^^ d_C1) 31 + d_σ) % 2 ^ 64 ≠ (rotl (CFA ^^^ d_C2) 31 + d_σ) % 2 ^ 64 := by
  have h := cfa_next_inj_in_cfa d_C1 d_C2 CFA d_σ h_diff hdC1 hdC2 hCFA
  -- h: (rotl (d_C1 ^^^ CFA) 31 + d_σ) % 2^64 ≠ (rotl (d_C2 ^^^ CFA) 31 + d_σ) % 2^64
  simpa [Nat.xor_comm CFA d_C1, Nat.xor_comm CFA d_C2] using h

-- ── P3d–f: H → δ 横向级联 ─────────────────────────────────────────
--
-- 若 h_next1 ≠ h_next2，则 d_σ / d_C / d_D 各不同（qAvalanche_inj）
-- XOR AC 使用 xor_cancel_right + xor_assoc 避免 simp 递归

private theorem xor_quad_cancel (a b c d : Nat) : (a ^^^ b ^^^ c ^^^ d) ^^^ a = b ^^^ c ^^^ d := by
  have h_reassoc : a ^^^ b ^^^ c ^^^ d = a ^^^ (b ^^^ c ^^^ d) := by
    calc
      a ^^^ b ^^^ c ^^^ d = (((a ^^^ b) ^^^ c) ^^^ d) := rfl
      _ = ((a ^^^ b) ^^^ (c ^^^ d)) := by rw [Nat.xor_assoc]
      _ = a ^^^ (b ^^^ (c ^^^ d)) := by rw [Nat.xor_assoc]
      _ = a ^^^ (b ^^^ c ^^^ d) := by rw [← Nat.xor_assoc b c d]
  calc
    (a ^^^ b ^^^ c ^^^ d) ^^^ a = (a ^^^ (b ^^^ c ^^^ d)) ^^^ a := by rw [h_reassoc]
    _ = b ^^^ c ^^^ d := by rw [(xor_cancel_right a (b ^^^ c ^^^ d)).symm]

theorem d_sigma_inj_in_hnext (z_hi h1 h2 r0 salt : Nat) (q : QAvalancheConfig) (invMult : Nat)
    (h_diff : h1 ≠ h2) (h1_lt : h1 < 2 ^ 64) (h2_lt : h2 < 2 ^ 64)
    (hz_hi : z_hi < 2 ^ 64) (hr0 : r0 < 2 ^ 64) (hsalt : salt < 2 ^ 64)
    (h_inv : (q.mult * invMult) % (2 ^ 64) = 1) (h_shift : 1 ≤ q.xor_shift) :
    qAvalanche (z_hi ^^^ h1 ^^^ r0 ^^^ salt) q ≠ qAvalanche (z_hi ^^^ h2 ^^^ r0 ^^^ salt) q := by
  intro h_eq
  have h_in1_lt : z_hi ^^^ h1 ^^^ r0 ^^^ salt < 2 ^ 64 := by
    have h1' : z_hi ^^^ h1 < 2 ^ 64 := xor_lt_two_pow _ _ 64 hz_hi h1_lt
    have h2' : r0 ^^^ salt < 2 ^ 64 := xor_lt_two_pow _ _ 64 hr0 hsalt
    simpa [Nat.xor_assoc] using xor_lt_two_pow _ _ 64 h1' h2'
  have h_in2_lt : z_hi ^^^ h2 ^^^ r0 ^^^ salt < 2 ^ 64 := by
    have h1' : z_hi ^^^ h2 < 2 ^ 64 := xor_lt_two_pow _ _ 64 hz_hi h2_lt
    have h2' : r0 ^^^ salt < 2 ^ 64 := xor_lt_two_pow _ _ 64 hr0 hsalt
    simpa [Nat.xor_assoc] using xor_lt_two_pow _ _ 64 h1' h2'
  have h_input_eq : z_hi ^^^ h1 ^^^ r0 ^^^ salt = z_hi ^^^ h2 ^^^ r0 ^^^ salt :=
    qAvalanche_inj _ _ q invMult h_eq h_in1_lt h_in2_lt h_inv h_shift
  have h_h_eq : h1 = h2 :=
    xor_inj h1 h2 (r0 ^^^ salt) (by
      calc
        h1 ^^^ (r0 ^^^ salt) = h1 ^^^ r0 ^^^ salt := by rw [Nat.xor_assoc]
        _ = ((z_hi ^^^ h1 ^^^ r0 ^^^ salt) ^^^ z_hi) := by rw [(xor_quad_cancel z_hi h1 r0 salt).symm]
        _ = ((z_hi ^^^ h2 ^^^ r0 ^^^ salt) ^^^ z_hi) := by rw [h_input_eq]
        _ = h2 ^^^ r0 ^^^ salt := by rw [xor_quad_cancel z_hi h2 r0 salt]
        _ = h2 ^^^ (r0 ^^^ salt) := by rw [Nat.xor_assoc])
  exact h_diff h_h_eq

theorem d_cfa_inj_in_hnext (z_lo h1 h2 edge salt : Nat) (q : QAvalancheConfig) (invMult : Nat)
    (h_diff : h1 ≠ h2) (h1_lt : h1 < 2 ^ 64) (h2_lt : h2 < 2 ^ 64)
    (hz_lo : z_lo < 2 ^ 64) (hedge : edge < 2 ^ 64) (hsalt : salt < 2 ^ 64)
    (h_inv : (q.mult * invMult) % (2 ^ 64) = 1) (h_shift : 1 ≤ q.xor_shift) :
    qAvalanche (rotl z_lo 23 ^^^ h1 ^^^ edge ^^^ salt) q ≠ qAvalanche (rotl z_lo 23 ^^^ h2 ^^^ edge ^^^ salt) q := by
  intro h_eq
  have h_zlo_lt : rotl z_lo 23 < 2 ^ 64 := rotl_lt_two_pow z_lo 23 hz_lo
  have h_in1_lt : rotl z_lo 23 ^^^ h1 ^^^ edge ^^^ salt < 2 ^ 64 := by
    have h1' : rotl z_lo 23 ^^^ h1 < 2 ^ 64 := xor_lt_two_pow _ _ 64 h_zlo_lt h1_lt
    have h2' : edge ^^^ salt < 2 ^ 64 := xor_lt_two_pow _ _ 64 hedge hsalt
    simpa [Nat.xor_assoc] using xor_lt_two_pow _ _ 64 h1' h2'
  have h_in2_lt : rotl z_lo 23 ^^^ h2 ^^^ edge ^^^ salt < 2 ^ 64 := by
    have h1' : rotl z_lo 23 ^^^ h2 < 2 ^ 64 := xor_lt_two_pow _ _ 64 h_zlo_lt h2_lt
    have h2' : edge ^^^ salt < 2 ^ 64 := xor_lt_two_pow _ _ 64 hedge hsalt
    simpa [Nat.xor_assoc] using xor_lt_two_pow _ _ 64 h1' h2'
  have h_input_eq : rotl z_lo 23 ^^^ h1 ^^^ edge ^^^ salt = rotl z_lo 23 ^^^ h2 ^^^ edge ^^^ salt :=
    qAvalanche_inj _ _ q invMult h_eq h_in1_lt h_in2_lt h_inv h_shift
  have h_h_eq : h1 = h2 :=
    xor_inj h1 h2 (edge ^^^ salt) (by
      calc
        h1 ^^^ (edge ^^^ salt) = h1 ^^^ edge ^^^ salt := by rw [Nat.xor_assoc]
        _ = ((rotl z_lo 23 ^^^ h1 ^^^ edge ^^^ salt) ^^^ rotl z_lo 23) := by
          rw [(xor_quad_cancel (rotl z_lo 23) h1 edge salt).symm]
        _ = ((rotl z_lo 23 ^^^ h2 ^^^ edge ^^^ salt) ^^^ rotl z_lo 23) := by rw [h_input_eq]
        _ = h2 ^^^ edge ^^^ salt := by rw [xor_quad_cancel (rotl z_lo 23) h2 edge salt]
        _ = h2 ^^^ (edge ^^^ salt) := by rw [Nat.xor_assoc])
  exact h_diff h_h_eq

theorem d_ddm_inj_in_hnext (z_lo z_hi h1 h2 ctr salt : Nat) (q : QAvalancheConfig) (invMult : Nat)
    (h_diff : h1 ≠ h2) (h1_lt : h1 < 2 ^ 64) (h2_lt : h2 < 2 ^ 64)
    (hz_sum : (z_lo + z_hi) % 2 ^ 64 < 2 ^ 64) (hctr : ctr < 2 ^ 64) (hsalt : salt < 2 ^ 64)
    (h_inv : (q.mult * invMult) % (2 ^ 64) = 1) (h_shift : 1 ≤ q.xor_shift) :
    qAvalanche ((z_lo + z_hi) % 2 ^ 64 ^^^ h1 ^^^ ctr ^^^ salt) q ≠ qAvalanche ((z_lo + z_hi) % 2 ^ 64 ^^^ h2 ^^^ ctr ^^^ salt) q := by
  intro h_eq
  let ddm := (z_lo + z_hi) % 2 ^ 64
  have h_in1_lt : ddm ^^^ h1 ^^^ ctr ^^^ salt < 2 ^ 64 := by
    have h1' : ddm ^^^ h1 < 2 ^ 64 := xor_lt_two_pow _ _ 64 hz_sum h1_lt
    have h2' : ctr ^^^ salt < 2 ^ 64 := xor_lt_two_pow _ _ 64 hctr hsalt
    simpa [Nat.xor_assoc] using xor_lt_two_pow _ _ 64 h1' h2'
  have h_in2_lt : ddm ^^^ h2 ^^^ ctr ^^^ salt < 2 ^ 64 := by
    have h1' : ddm ^^^ h2 < 2 ^ 64 := xor_lt_two_pow _ _ 64 hz_sum h2_lt
    have h2' : ctr ^^^ salt < 2 ^ 64 := xor_lt_two_pow _ _ 64 hctr hsalt
    simpa [Nat.xor_assoc] using xor_lt_two_pow _ _ 64 h1' h2'
  have h_input_eq : ddm ^^^ h1 ^^^ ctr ^^^ salt = ddm ^^^ h2 ^^^ ctr ^^^ salt :=
    qAvalanche_inj _ _ q invMult h_eq h_in1_lt h_in2_lt h_inv h_shift
  have h_h_eq : h1 = h2 :=
    xor_inj h1 h2 (ctr ^^^ salt) (by
      calc
        h1 ^^^ (ctr ^^^ salt) = h1 ^^^ ctr ^^^ salt := by rw [Nat.xor_assoc]
        _ = ((ddm ^^^ h1 ^^^ ctr ^^^ salt) ^^^ ddm) := by rw [(xor_quad_cancel ddm h1 ctr salt).symm]
        _ = ((ddm ^^^ h2 ^^^ ctr ^^^ salt) ^^^ ddm) := by rw [h_input_eq]
        _ = h2 ^^^ ctr ^^^ salt := by rw [xor_quad_cancel ddm h2 ctr salt]
        _ = h2 ^^^ (ctr ^^^ salt) := by rw [Nat.xor_assoc])
  exact h_diff h_h_eq

-- ── G2: Joint Cascade (h divergence → all 7 outputs diverge) ──────────
--
-- If h1 ≠ h2 (all other state inputs identical), then every output of
-- `update_state` diverges: h_next, d_σ, d_C, d_D, σ_next, CFA_next, DDM_next.
--
-- The state field divergence requires new lemmas because when h_next differs,
-- ALL δ values differ simultaneously, so the existing per-channel injectivity
-- lemmas (which assume the other δ is constant) don't directly apply.
--
-- For σ_next = rotl(σ + d_σ, 17) ^^^ d_D:
--   The map (d_σ, d_D) → rotl(σ + d_σ, 17) ^^^ d_D is NOT injective in general
--   (counterexample: σ=0, d_σ1=1, d_D1=3, d_σ2=2, d_D2=0 → both give 131072).
--   However, in our case (d_σ, d_D) are derived from h_next via qAvalanche,
--   which constrains the relationship. Proving σ_next divergence requires
--   analyzing the joint distribution of (d_σ, d_D) across h_next values.
--
-- Strategy: prove the 4 most important outputs (h_next, d_σ, d_C, d_D) diverge,
-- then prove state fields using helper lemmas that handle dual-δ divergence.

-- ── Helper: σ_next divergence when d_σ AND d_D both differ ───────────
--
-- σ_next = rotl(σ + d_σ, 17) ^^^ d_D
-- When d_σ1 ≠ d_σ2: let A1 = rotl(σ + d_σ1, 17), A2 = rotl(σ + d_σ2, 17). A1 ≠ A2.
-- σ_next1 = A1 ^^^ d_D1, σ_next2 = A2 ^^^ d_D2.
-- If σ_next1 = σ_next2, then A1 ^^^ d_D1 = A2 ^^^ d_D2.
-- XOR with A1: d_D1 = A1 ^^^ A2 ^^^ d_D2. (determined by d_σ1, d_σ2, d_D2)
-- This is consistent, so we need additional structure.
--
-- Key: d_σ = qAvalanche(input_σ, q_σ) and d_D = qAvalanche(input_D, q_D)
-- where input_σ = z_hi ^^^ h_next ^^^ r0 ^^^ salt
-- and   input_D = (z_lo+z_hi)%2^64 ^^^ h_next ^^^ ctr ^^^ salt.
-- When h_next1 ≠ h_next2, both inputs change by the SAME delta (h_next1^^^h_next2).
-- qAvalanche is a bijection, so (d_σ1, d_D1) ≠ (d_σ2, d_D2) (component-wise).
-- But this still doesn't directly give σ_next divergence.

-- ── Helper: CFA_next divergence when d_C AND d_σ both differ ──────────
--
-- CFA_next = (rotl(CFA ^^^ d_C, 31) + d_σ) % 2^64
-- When d_C1 ≠ d_C2: let A1 = rotl(CFA ^^^ d_C1, 31), A2 = rotl(CFA ^^^ d_C2, 31). A1 ≠ A2.
-- CFA_next1 = (A1 + d_σ1) % 2^64, CFA_next2 = (A2 + d_σ2) % 2^64.
-- Same issue: not injective when both d_C and d_σ differ.

-- ── Helper: DDM_next divergence when d_D AND d_C both differ ──────────
--
-- DDM_next = rotl(DDM + d_D, 47) ^^^ d_C
-- Same structure as σ_next: map (d_D, d_C) → rotl(DDM + d_D, 47) ^^^ d_C is not injective.

-- ── T14_joint_cascade: h divergence → 4 core outputs diverge ──────────
--
-- This is the strongest result provable with current per-channel lemmas.
-- It proves h_next, d_σ, d_C, d_D diverge. The state field divergence
-- (σ_next, CFA_next, DDM_next) follows from additional analysis of the
-- joint (d_σ, d_D) distribution, deferred to a future enhancement.

theorem T14_joint_cascade
    (σ CFA DDM h1 h2 z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt : Nat)
    (q_h q_sigma q_cfa q_ddm : QAvalancheConfig)
    (invMult_h invMult_sigma invMult_cfa invMult_ddm : Nat)
    (h_diff : h1 ≠ h2)
    (h1_lt : h1 < 2 ^ 64) (h2_lt : h2 < 2 ^ 64)
    (hz_lo : z_lo < 2 ^ 64) (hz_hi : z_hi < 2 ^ 64)
    (hrb : rb_val < 2 ^ 64)
    (hres : result < 2 ^ 64) (hedge : edge < 2 ^ 64)
    (hmem : mem < 2 ^ 64) (hcall : call < 2 ^ 64)
    (hspawn : spawn < 2 ^ 64) (hent : ent_mix < 2 ^ 64)
    (hctr : ctr < 2 ^ 64) (hr0 : r0 < 2 ^ 64) (hsalt : salt < 2 ^ 64)
    (h_inv_h : (q_h.mult * invMult_h) % (2 ^ 64) = 1) (h_shift_h : 1 ≤ q_h.xor_shift)
    (h_inv_sigma : (q_sigma.mult * invMult_sigma) % (2 ^ 64) = 1) (h_shift_sigma : 1 ≤ q_sigma.xor_shift)
    (h_inv_cfa : (q_cfa.mult * invMult_cfa) % (2 ^ 64) = 1) (h_shift_cfa : 1 ≤ q_cfa.xor_shift)
    (h_inv_ddm : (q_ddm.mult * invMult_ddm) % (2 ^ 64) = 1) (h_shift_ddm : 1 ≤ q_ddm.xor_shift) :
    let s1 := update_state σ CFA DDM h1 z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt q_h q_sigma q_cfa q_ddm
    let s2 := update_state σ CFA DDM h2 z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt q_h q_sigma q_cfa q_ddm
    s1.h_next ≠ s2.h_next ∧
    s1.d_sigma ≠ s2.d_sigma ∧
    s1.d_cfa ≠ s2.d_cfa ∧
    s1.d_ddm ≠ s2.d_ddm := by
  unfold update_state
  -- h_next diverges (update_h_inj_in_h)
  have h_hnext_diff :
      update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h ≠
      update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h := by
    exact update_h_inj_in_h h1 h2 ra_val rb_val result edge mem call spawn ent_mix q_h invMult_h
      h_diff h1_lt h2_lt hrb hres hedge hmem hcall hspawn hent h_inv_h h_shift_h
  have h_hnext1_lt : update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h < 2 ^ 64 :=
    update_h_lt_two_pow h1 ra_val rb_val result edge mem call spawn ent_mix q_h
  have h_hnext2_lt : update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h < 2 ^ 64 :=
    update_h_lt_two_pow h2 ra_val rb_val result edge mem call spawn ent_mix q_h
  -- d_σ diverges (d_sigma_inj_in_hnext)
  have h_dσ_diff :
      qAvalanche (z_hi ^^^ update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h ^^^ r0 ^^^ salt) q_sigma ≠
      qAvalanche (z_hi ^^^ update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h ^^^ r0 ^^^ salt) q_sigma := by
    exact d_sigma_inj_in_hnext z_hi
      (update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h)
      (update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h)
      r0 salt q_sigma invMult_sigma
      h_hnext_diff h_hnext1_lt h_hnext2_lt hz_hi hr0 hsalt h_inv_sigma h_shift_sigma
  -- d_C diverges (d_cfa_inj_in_hnext)
  have h_dC_diff :
      qAvalanche (rotl z_lo 23 ^^^ update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h ^^^ edge ^^^ salt) q_cfa ≠
      qAvalanche (rotl z_lo 23 ^^^ update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h ^^^ edge ^^^ salt) q_cfa := by
    exact d_cfa_inj_in_hnext z_lo
      (update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h)
      (update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h)
      edge salt q_cfa invMult_cfa
      h_hnext_diff h_hnext1_lt h_hnext2_lt hz_lo hedge hsalt h_inv_cfa h_shift_cfa
  -- d_D diverges (d_ddm_inj_in_hnext)
  have h_dD_diff :
      qAvalanche ((z_lo + z_hi) % 2 ^ 64 ^^^ update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h ^^^ ctr ^^^ salt) q_ddm ≠
      qAvalanche ((z_lo + z_hi) % 2 ^ 64 ^^^ update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h ^^^ ctr ^^^ salt) q_ddm := by
    exact d_ddm_inj_in_hnext z_lo z_hi
      (update_h h1 ra_val rb_val result edge mem call spawn ent_mix q_h)
      (update_h h2 ra_val rb_val result edge mem call spawn ent_mix q_h)
      ctr salt q_ddm invMult_ddm
      h_hnext_diff h_hnext1_lt h_hnext2_lt
      (Nat.mod_lt _ (Nat.two_pow_pos 64))
      hctr hsalt h_inv_ddm h_shift_ddm
  exact ⟨h_hnext_diff, h_dσ_diff, h_dC_diff, h_dD_diff⟩
