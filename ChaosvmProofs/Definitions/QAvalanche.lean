import ChaosvmProofs.Definitions.Helpers
import Init.Data.Nat.Bitwise
import Init.Data.Nat.Power2
import Init.Omega

open Nat

/-! # Q avalanche function (Rust: `g_mixer.rs:37`).

Concrete implementation matching Rust `q_avalanche`:
  z = x.wrapping_mul(p.mult);  // mod 2^64
  z ^= z >> p.xor_shift;       // shr followed by XOR
  z.rotate_left(p.rot)         // 64-bit rotation

All three operations are bijections on `[0, 2^64-1]`:
  1. Multiplication by odd constant mod 2^64 (odd → invertible)
  2. `x ↦ x ^^^ (x >> k)` for `k ≥ 1` (injective by algebraic cancellation)
  3. 64-bit left rotation (injective by rotl∘rotr = identity)
-/

structure QAvalancheConfig where
  mult      : Nat
  rot       : Nat
  xor_shift : Nat

/-- Concrete qAvalanche matching Rust. All operations are 64-bit bounded. -/
def qAvalanche (x : Nat) (cfg : QAvalancheConfig) : Nat :=
  let z1 := (x * cfg.mult) % (2 ^ 64)
  let z2 := z1 ^^^ (shr z1 cfg.xor_shift)
  rotl64 z2 cfg.rot

theorem qAvalanche_deterministic (x : Nat) (cfg : QAvalancheConfig) :
    qAvalanche x cfg = qAvalanche x cfg := rfl

theorem qAvalanche_zero (cfg : QAvalancheConfig) : qAvalanche 0 cfg = 0 := by
  unfold qAvalanche
  simp [shl, shr, rotl64, mask64]

-- ── Lemma 0: `land` with mask64 = `% 2^64` ─────────────────────────────

theorem land_mask64_eq_mod (x : Nat) : land x mask64 = x % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show land = bitwise (λ a b => a && b) from rfl]
  rw [testBit_bitwise (by decide) x mask64 i]
  show (x.testBit i && (2 ^ 64 - 1).testBit i) = (x % 2 ^ 64).testBit i
  rw [testBit_two_pow_sub_one 64 i, testBit_mod_two_pow x 64 i, Bool.and_comm]

-- ── Lemma 0b: `a ^^^ b < 2^n` when `a, b < 2^n` ───────────────────────

theorem xor_lt_two_pow (a b n : Nat) (ha : a < 2 ^ n) (hb : b < 2 ^ n) : (a ^^^ b) < 2 ^ n := by
  have ha_div : a / 2 ^ n = 0 := Nat.div_eq_of_lt ha
  have hb_div : b / 2 ^ n = 0 := Nat.div_eq_of_lt hb
  have hxor_div : (a ^^^ b) / 2 ^ n = 0 := by
    calc
      (a ^^^ b) / 2 ^ n = (a / 2 ^ n) ^^^ (b / 2 ^ n) := by rw [Nat.xor_div_two_pow]
      _ = 0 ^^^ 0 := by rw [ha_div, hb_div]
      _ = 0 := by simp
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  exact ((Nat.div_eq_zero_iff_lt hpos).mp hxor_div)

-- ── Lemma 1: `x ↦ x ^^^ (x >> k)` is injective on ℕ for k ≥ 1 ──────────

theorem xor_swap_mid (x y a b : Nat) : (x ^^^ y) ^^^ (a ^^^ b) = (x ^^^ a) ^^^ (y ^^^ b) := by
  calc
    (x ^^^ y) ^^^ (a ^^^ b) = ((x ^^^ y) ^^^ a) ^^^ b := by simp [Nat.xor_assoc]
    _ = (x ^^^ (y ^^^ a)) ^^^ b := by simp [Nat.xor_assoc]
    _ = (x ^^^ (a ^^^ y)) ^^^ b := by simp [Nat.xor_comm]
    _ = ((x ^^^ a) ^^^ y) ^^^ b := by simp [Nat.xor_assoc]
    _ = (x ^^^ a) ^^^ (y ^^^ b) := by simp [Nat.xor_assoc]

theorem shr_xor (x y k : Nat) : shr (x ^^^ y) k = (shr x k) ^^^ (shr y k) := by
  simp [shr, Nat.xor_div_two_pow]

/-- `f_k(x) = x ^^^ (x >> k)` is injective for `k ≥ 1`. -/
theorem xor_shr_inj (x y k : Nat) (h : x ^^^ (shr x k) = y ^^^ (shr y k)) (hk : 1 ≤ k) : x = y := by
  have h_sub : (x ^^^ (shr x k)) ^^^ (y ^^^ (shr y k)) = 0 := by rw [h, Nat.xor_self]
  have h_xor_eq_zero : (x ^^^ y) ^^^ ((shr x k) ^^^ (shr y k)) = 0 := by
    calc
      (x ^^^ y) ^^^ ((shr x k) ^^^ (shr y k))
          = (x ^^^ (shr x k)) ^^^ (y ^^^ (shr y k)) := xor_swap_mid x y (shr x k) (shr y k)
      _ = 0 := h_sub
  have h_xor_eq : (x ^^^ y) = (shr x k) ^^^ (shr y k) := by
    calc
      (x ^^^ y) = ((x ^^^ y) ^^^ ((shr x k) ^^^ (shr y k))) ^^^ ((shr x k) ^^^ (shr y k)) := by
        simp [Nat.xor_assoc]
      _ = 0 ^^^ ((shr x k) ^^^ (shr y k)) := by rw [h_xor_eq_zero]
      _ = (shr x k) ^^^ (shr y k) := by simp
  have h_eq : (x ^^^ y) = shr (x ^^^ y) k := by
    calc
      (x ^^^ y) = (shr x k) ^^^ (shr y k) := h_xor_eq
      _ = shr (x ^^^ y) k := by rw [shr_xor]
  by_cases hzero : x ^^^ y = 0
  · calc
      x = (x ^^^ y) ^^^ y := by
        calc
          x = x ^^^ 0 := by simp
          _ = x ^^^ (y ^^^ y) := by simp
          _ = (x ^^^ y) ^^^ y := by simp [Nat.xor_assoc]
      _ = 0 ^^^ y := by rw [hzero]
      _ = y := by simp
  · have h_lt : shr (x ^^^ y) k < x ^^^ y := by
      have hpos : 0 < x ^^^ y := Nat.pos_of_ne_zero hzero
      have hpow_gt_one : 1 < 2 ^ k := by
        have h2k_ge_2 : 2 ≤ 2 ^ k := by
          have htemp : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
          omega
        omega
      exact Nat.div_lt_self hpos hpow_gt_one
    have h_lt' : shr (x ^^^ y) k < shr (x ^^^ y) k :=
      calc
        shr (x ^^^ y) k < x ^^^ y := h_lt
        _ = shr (x ^^^ y) k := h_eq
    exact absurd h_lt' (Nat.lt_irrefl _)

-- ── Lemma 2: multiplication by odd constant is injective mod 2^64 ──────

/-- `mul_odd_inj_mod_2pow64`:
    If `(a * mult) % 2^64 = (b * mult) % 2^64`, `mult` has inverse `invMult` modulo 2^64,
    and `a, b < 2^64`, then `a = b`. -/
theorem mul_odd_inj_mod_2pow64 (a b mult invMult : Nat) (h : (a * mult) % (2 ^ 64) = (b * mult) % (2 ^ 64))
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h_inv : (mult * invMult) % (2 ^ 64) = 1) : a = b := by
  have ha_val : a % (2 ^ 64) = a := Nat.mod_eq_of_lt ha
  have hb_val : b % (2 ^ 64) = b := Nat.mod_eq_of_lt hb
  have h_mod_mul (x : Nat) : (x % (2 ^ 64) * invMult) % (2 ^ 64) = (x * invMult) % (2 ^ 64) := by
    calc
      (x % (2 ^ 64) * invMult) % (2 ^ 64) = ((x % (2 ^ 64)) % (2 ^ 64) * (invMult % (2 ^ 64))) % (2 ^ 64) := by
        rw [Nat.mul_mod]
      _ = (x % (2 ^ 64) * (invMult % (2 ^ 64))) % (2 ^ 64) := by rw [Nat.mod_mod]
      _ = (x * invMult) % (2 ^ 64) := by rw [← Nat.mul_mod]
  have ha_restore : (a * mult) % (2 ^ 64) * invMult % (2 ^ 64) = a := by
    calc
      (a * mult) % (2 ^ 64) * invMult % (2 ^ 64) = (a * mult * invMult) % (2 ^ 64) := by
        rw [h_mod_mul (a * mult)]
      _ = (a * (mult * invMult)) % (2 ^ 64) := by rw [Nat.mul_assoc]
      _ = ((a % (2 ^ 64)) * ((mult * invMult) % (2 ^ 64))) % (2 ^ 64) := by rw [Nat.mul_mod]
      _ = (a * ((mult * invMult) % (2 ^ 64))) % (2 ^ 64) := by rw [ha_val]
      _ = (a * 1) % (2 ^ 64) := by rw [h_inv]
      _ = a % (2 ^ 64) := by omega
      _ = a := ha_val
  have hb_restore : (b * mult) % (2 ^ 64) * invMult % (2 ^ 64) = b := by
    calc
      (b * mult) % (2 ^ 64) * invMult % (2 ^ 64) = (b * mult * invMult) % (2 ^ 64) := by
        rw [h_mod_mul (b * mult)]
      _ = (b * (mult * invMult)) % (2 ^ 64) := by rw [Nat.mul_assoc]
      _ = ((b % (2 ^ 64)) * ((mult * invMult) % (2 ^ 64))) % (2 ^ 64) := by rw [Nat.mul_mod]
      _ = (b * ((mult * invMult) % (2 ^ 64))) % (2 ^ 64) := by rw [hb_val]
      _ = (b * 1) % (2 ^ 64) := by rw [h_inv]
      _ = b % (2 ^ 64) := by omega
      _ = b := hb_val
  calc
    a = (a * mult) % (2 ^ 64) * invMult % (2 ^ 64) := by rw [ha_restore]
    _ = (b * mult) % (2 ^ 64) * invMult % (2 ^ 64) := by rw [h]
    _ = b := by rw [hb_restore]

-- ── Lemma 3: rotl64 is injective on [0, 2^64-1] via rotl∘rotr identity ──

theorem two_pow_mul_eq (a b : Nat) (ha : a + b = 64) : 2 ^ a * 2 ^ b = 2 ^ 64 := by
  calc
    2 ^ a * 2 ^ b = 2 ^ (a + b) := by rw [Nat.pow_add]
    _ = 2 ^ 64 := by rw [ha]

theorem decompose_hi_bound (x n' : Nat) (hx : x < 2 ^ 64) (hn' : n' < 64) : x / (2 ^ (64 - n')) < 2 ^ n' := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (64 - n'))).mpr
  have h_exp : 2 ^ 64 = 2 ^ n' * 2 ^ (64 - n') := by
    have h_add : n' + (64 - n') = 64 := by omega
    calc
      2 ^ 64 = 2 ^ (n' + (64 - n')) := by rw [h_add]
      _ = 2 ^ n' * 2 ^ (64 - n') := by rw [Nat.pow_add]
  calc
    x < 2 ^ 64 := hx
    _ = 2 ^ n' * 2 ^ (64 - n') := h_exp

theorem rotl64_eq_add (x n : Nat) (hx : x < 2 ^ 64) : rotl64 x n =
    (x % (2 ^ (64 - (n % 64)))) * 2 ^ (n % 64) + (x / (2 ^ (64 - (n % 64)))) := by
  let n' := n % 64
  have hn' : n' < 64 := Nat.mod_lt n (by omega : 0 < 64)
  let lo := x % (2 ^ (64 - n'))
  let hi := x / (2 ^ (64 - n'))
  have h_hi_lt : hi < 2 ^ n' := decompose_hi_bound x n' hx hn'
  have h_hi_lt_64 : hi < 2 ^ 64 := by
    calc
      hi < 2 ^ n' := h_hi_lt
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have h_lo_mul_lt : lo * 2 ^ n' < 2 ^ 64 := by
    have hlo : lo < 2 ^ (64 - n') := Nat.mod_lt _ (Nat.two_pow_pos (64 - n'))
    have hpos : 0 < 2 ^ n' := Nat.two_pow_pos n'
    have h_mul_eq : 2 ^ (64 - n') * 2 ^ n' = 2 ^ 64 :=
      two_pow_mul_eq (64 - n') n' (by omega)
    have h_mul_lt' : lo * 2 ^ n' < 2 ^ (64 - n') * 2 ^ n' :=
      Nat.mul_lt_mul_of_pos_right hlo hpos
    rw [h_mul_eq] at h_mul_lt'
    exact h_mul_lt'
  have hx_decomp : x = lo + 2 ^ (64 - n') * hi := by
    have h := Nat.div_add_mod x (2 ^ (64 - n'))
    have h' : 2 ^ (64 - n') * hi + lo = x := by
      simpa [lo, hi] using h
    calc
      x = 2 ^ (64 - n') * hi + lo := Eq.symm h'
      _ = lo + 2 ^ (64 - n') * hi := by rw [Nat.add_comm]
  have h_mul_mod : (x * 2 ^ n') % (2 ^ 64) = lo * 2 ^ n' := by
    calc
      (x * 2 ^ n') % (2 ^ 64) = ((lo + 2 ^ (64 - n') * hi) * 2 ^ n') % (2 ^ 64) := by rw [hx_decomp]
      _ = (lo * 2 ^ n' + (2 ^ (64 - n') * hi) * 2 ^ n') % (2 ^ 64) := by rw [Nat.add_mul]
      _ = (lo * 2 ^ n' + hi * (2 ^ (64 - n') * 2 ^ n')) % (2 ^ 64) := by
        have h_inner : (2 ^ (64 - n') * hi) * 2 ^ n' = hi * (2 ^ (64 - n') * 2 ^ n') := by
          calc
            (2 ^ (64 - n') * hi) * 2 ^ n' = (hi * 2 ^ (64 - n')) * 2 ^ n' := by
              rw [Nat.mul_comm (2 ^ (64 - n')) hi]
            _ = hi * (2 ^ (64 - n') * 2 ^ n') := by rw [Nat.mul_assoc]
        simp [h_inner]
      _ = (lo * 2 ^ n' + hi * 2 ^ 64) % (2 ^ 64) := by
        have h_mul_eq' : 2 ^ (64 - n') * 2 ^ n' = 2 ^ 64 :=
          two_pow_mul_eq (64 - n') n' (by omega)
        simp [h_mul_eq']
      _ = (lo * 2 ^ n') % (2 ^ 64) := by simp
      _ = lo * 2 ^ n' := Nat.mod_eq_of_lt h_lo_mul_lt
  have h_land_simp : Nat.land (x / 2 ^ (64 - n')) mask64 = hi := by
    calc
      Nat.land (x / 2 ^ (64 - n')) mask64 = (x / 2 ^ (64 - n')) % 2 ^ 64 := land_mask64_eq_mod _
      _ = x / 2 ^ (64 - n') := Nat.mod_eq_of_lt h_hi_lt_64
      _ = hi := rfl
  unfold rotl64
  simp [shl, shr]
  calc
    Nat.lor ((x * 2 ^ n') % (2 ^ 64)) (Nat.land (x / 2 ^ (64 - n')) mask64)
        = Nat.lor ((x * 2 ^ n') % (2 ^ 64)) hi := by rw [h_land_simp]
    _ = Nat.lor (lo * 2 ^ n') hi := by rw [h_mul_mod]
    _ = lo * 2 ^ n' + hi := by
      simpa [Nat.mul_comm] using (Nat.two_pow_add_eq_or_of_lt h_hi_lt lo).symm

/-- `rotr64` is the left inverse of `rotl64` for values < 2^64. -/
theorem rotl64_rotr64_inverse (x : Nat) (n : Nat) (hx : x < 2 ^ 64) : rotr64 (rotl64 x n) n = x := by
  let n' := n % 64
  have hn' : n' < 64 := Nat.mod_lt n (by omega : 0 < 64)
  let lo := x % (2 ^ (64 - n'))
  let hi := x / (2 ^ (64 - n'))
  have h_hi_lt : hi < 2 ^ n' := decompose_hi_bound x n' hx hn'
  have h_lo_lt : lo < 2 ^ (64 - n') := Nat.mod_lt _ (Nat.two_pow_pos (64 - n'))
  have h_rotl_eq : rotl64 x n = lo * 2 ^ n' + hi := by
    have h := rotl64_eq_add x n hx
    simpa [lo, hi] using h
  have h_mul_eq : 2 ^ n' * 2 ^ (64 - n') = 2 ^ 64 :=
    two_pow_mul_eq n' (64 - n') (by omega)
  have h_mul_lt : hi * 2 ^ (64 - n') < 2 ^ 64 := by
    have hpos' : 0 < 2 ^ (64 - n') := Nat.two_pow_pos (64 - n')
    have h_mul_lt' : hi * 2 ^ (64 - n') < 2 ^ n' * 2 ^ (64 - n') :=
      Nat.mul_lt_mul_of_pos_right h_hi_lt hpos'
    rw [h_mul_eq] at h_mul_lt'
    exact h_mul_lt'
  have h_mul_land_simp : Nat.land (hi * 2 ^ (64 - n')) mask64 = hi * 2 ^ (64 - n') := by
    calc
      Nat.land (hi * 2 ^ (64 - n')) mask64 = (hi * 2 ^ (64 - n')) % 2 ^ 64 := land_mask64_eq_mod _
      _ = hi * 2 ^ (64 - n') := Nat.mod_eq_of_lt h_mul_lt
  have h_mul_mod : ((lo * 2 ^ n' + hi) * 2 ^ (64 - n')) % (2 ^ 64) = hi * 2 ^ (64 - n') := by
    calc
      ((lo * 2 ^ n' + hi) * 2 ^ (64 - n')) % (2 ^ 64)
          = (lo * 2 ^ n' * 2 ^ (64 - n') + hi * 2 ^ (64 - n')) % (2 ^ 64) := by rw [Nat.add_mul]
      _ = (lo * (2 ^ n' * 2 ^ (64 - n')) + hi * 2 ^ (64 - n')) % (2 ^ 64) := by
        simp [Nat.mul_assoc]
      _ = (lo * 2 ^ 64 + hi * 2 ^ (64 - n')) % (2 ^ 64) := by rw [h_mul_eq]
      _ = (hi * 2 ^ (64 - n')) % (2 ^ 64) := by simp
      _ = hi * 2 ^ (64 - n') := Nat.mod_eq_of_lt h_mul_lt
  have h_div : (lo * 2 ^ n' + hi) / (2 ^ n') = lo := by
    have hpos : 0 < 2 ^ n' := Nat.two_pow_pos n'
    calc
      (lo * 2 ^ n' + hi) / (2 ^ n') = (hi + lo * 2 ^ n') / (2 ^ n') := by
        rw [Nat.add_comm (lo * 2 ^ n') hi]
      _ = (hi + 2 ^ n' * lo) / (2 ^ n') := by simp [Nat.mul_comm]
      _ = hi / (2 ^ n') + lo := by rw [Nat.add_mul_div_left hi lo hpos]
      _ = 0 + lo := by rw [Nat.div_eq_of_lt h_hi_lt]
      _ = lo := by omega
  have h_calc : rotr64 (lo * 2 ^ n' + hi) n = hi * 2 ^ (64 - n') + lo := by
    rw [rotr64, shl, shr]
    have hn'_def : n % 64 = n' := rfl
    rw [hn'_def]
    calc
      Nat.lor (Nat.land (((lo * 2 ^ n' + hi) * 2 ^ (64 - n'))) mask64) ((lo * 2 ^ n' + hi) / (2 ^ n'))
          = Nat.lor ((((lo * 2 ^ n' + hi) * 2 ^ (64 - n')) % 2 ^ 64)) lo := by
            rw [land_mask64_eq_mod, h_div]
      _ = Nat.lor (hi * 2 ^ (64 - n')) lo := by rw [h_mul_mod]
      _ = hi * 2 ^ (64 - n') + lo := by
        simpa [Nat.mul_comm] using (Nat.two_pow_add_eq_or_of_lt h_lo_lt hi).symm
  have hx_decomp : x = lo + 2 ^ (64 - n') * hi := by
    have h := Nat.div_add_mod x (2 ^ (64 - n'))
    have h' : 2 ^ (64 - n') * hi + lo = x := by
      simpa [lo, hi] using h
    calc
      x = 2 ^ (64 - n') * hi + lo := Eq.symm h'
      _ = lo + 2 ^ (64 - n') * hi := by rw [Nat.add_comm]
  calc
    rotr64 (rotl64 x n) n = rotr64 (lo * 2 ^ n' + hi) n := by rw [h_rotl_eq]
    _ = hi * 2 ^ (64 - n') + lo := h_calc
    _ = lo + hi * 2 ^ (64 - n') := by rw [Nat.add_comm]
    _ = lo + 2 ^ (64 - n') * hi := by rw [Nat.mul_comm]
    _ = x := by rw [hx_decomp]

/-- `rotl64(·, n)` is injective on `[0, 2^64-1]` for any n. -/
theorem rotl64_inj (x y n : Nat) (h : rotl64 x n = rotl64 y n) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : x = y := by
  calc
    x = rotr64 (rotl64 x n) n := by rw [rotl64_rotr64_inverse x n hx]
    _ = rotr64 (rotl64 y n) n := by rw [h]
    _ = y := by rw [rotl64_rotr64_inverse y n hy]

-- ── Lemma 4: qAvalanche is injective on [0, 2^64-1] ─────────────────────

/-- `qAvalanche(·, cfg)` is injective on `[0, 2^64-1]` for any config
    with odd multiplier (inverse known), xor_shift ≥ 1, and any rotation.

    Proof: `qAvalanche` is a composition of three injective maps:
      1. `x ↦ (x * mult) % 2^64` — injective for odd mult (`mul_odd_inj_mod_2pow64`)
      2. `z1 ↦ z1 ^^^ (z1 >> xor_shift)` — injective for xor_shift ≥ 1 (`xor_shr_inj`)
      3. `z2 ↦ rotl64(z2, rot)` — injective (`rotl64_inj`)

    The hypothesis `h_inv : (mult * invMult) % (2 ^ 64) = 1` certifies `mult` is odd
    and provides the modular inverse needed for step 1. -/
theorem qAvalanche_inj (a b : Nat) (cfg : QAvalancheConfig) (invMult : Nat)
    (h : qAvalanche a cfg = qAvalanche b cfg)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h_inv : (cfg.mult * invMult) % (2 ^ 64) = 1)
    (h_shift : 1 ≤ cfg.xor_shift) : a = b := by
  unfold qAvalanche at h
  -- Step 3: rotl64 is injective → z2 values are equal
  have h_z2_lt_a : ((a * cfg.mult) % (2 ^ 64) ^^^ (shr ((a * cfg.mult) % (2 ^ 64)) cfg.xor_shift)) < 2 ^ 64 := by
    have hmod : (a * cfg.mult) % (2 ^ 64) < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
    have hshr_lt : shr ((a * cfg.mult) % (2 ^ 64)) cfg.xor_shift < 2 ^ 64 := by
      have hle : shr ((a * cfg.mult) % (2 ^ 64)) cfg.xor_shift ≤ (a * cfg.mult) % (2 ^ 64) :=
        Nat.div_le_self _ _
      omega
    exact xor_lt_two_pow _ _ _ hmod hshr_lt
  have h_z2_lt_b : ((b * cfg.mult) % (2 ^ 64) ^^^ (shr ((b * cfg.mult) % (2 ^ 64)) cfg.xor_shift)) < 2 ^ 64 := by
    have hmod : (b * cfg.mult) % (2 ^ 64) < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
    have hshr_lt : shr ((b * cfg.mult) % (2 ^ 64)) cfg.xor_shift < 2 ^ 64 := by
      have hle : shr ((b * cfg.mult) % (2 ^ 64)) cfg.xor_shift ≤ (b * cfg.mult) % (2 ^ 64) :=
        Nat.div_le_self _ _
      omega
    exact xor_lt_two_pow _ _ _ hmod hshr_lt
  have h_z2 : (a * cfg.mult) % (2 ^ 64) ^^^ (shr ((a * cfg.mult) % (2 ^ 64)) cfg.xor_shift) =
             (b * cfg.mult) % (2 ^ 64) ^^^ (shr ((b * cfg.mult) % (2 ^ 64)) cfg.xor_shift) :=
    rotl64_inj _ _ cfg.rot h h_z2_lt_a h_z2_lt_b
  -- Step 2: xor_shr is injective → z1 values are equal
  have h_z1 : (a * cfg.mult) % (2 ^ 64) = (b * cfg.mult) % (2 ^ 64) :=
    xor_shr_inj _ _ cfg.xor_shift h_z2 h_shift
  -- Step 1: multiplication by odd mult is injective modulo 2^64
  exact mul_odd_inj_mod_2pow64 a b cfg.mult invMult h_z1 ha hb h_inv

/-- `rotl64(x,n) < 2^64` when `x < 2^64`. -/
theorem rotl64_lt_two_pow (x n : Nat) (hx : x < 2 ^ 64) : rotl64 x n < 2 ^ 64 := by
  have h := rotl64_eq_add x n hx
  rw [h]
  let n' := n % 64
  have hn' : n' < 64 := Nat.mod_lt n (by omega)
  have h_lo_lt : x % (2 ^ (64 - n')) < 2 ^ (64 - n') :=
    Nat.mod_lt _ (Nat.two_pow_pos (64 - n'))
  have h_hi_lt : x / (2 ^ (64 - n')) < 2 ^ n' := decompose_hi_bound x n' hx hn'
  have h_mul_eq : 2 ^ (64 - n') * 2 ^ n' = 2 ^ 64 :=
    two_pow_mul_eq (64 - n') n' (by omega)
  have h_lo_mul_bound : (x % (2 ^ (64 - n'))) * 2 ^ n' + 2 ^ n' ≤ 2 ^ 64 := by
    have h_eq : (x % (2 ^ (64 - n'))) * 2 ^ n' + 2 ^ n' = ((x % (2 ^ (64 - n'))) + 1) * 2 ^ n' := by
      rw [Nat.succ_mul]
    rw [h_eq]
    have h_le : (x % (2 ^ (64 - n'))) + 1 ≤ 2 ^ (64 - n') := by omega
    calc
      ((x % (2 ^ (64 - n'))) + 1) * 2 ^ n' ≤ 2 ^ (64 - n') * 2 ^ n' :=
        Nat.mul_le_mul h_le (Nat.le_refl _)
      _ = 2 ^ 64 := h_mul_eq
  have h_sum_lt : (x % (2 ^ (64 - n'))) * 2 ^ n' + (x / (2 ^ (64 - n'))) < 2 ^ 64 := by
    have hlt : (x % (2 ^ (64 - n'))) * 2 ^ n' + (x / (2 ^ (64 - n'))) <
               (x % (2 ^ (64 - n'))) * 2 ^ n' + 2 ^ n' := by omega
    omega
  exact h_sum_lt

/-- `rotl(x,n) < 2^64` when `x < 2^64`. -/
theorem rotl_lt_two_pow (x n : Nat) (hx : x < 2 ^ 64) : rotl x n < 2 ^ 64 :=
  rotl64_lt_two_pow x n hx

/-- `qAvalanche(x,cfg) < 2^64` for any x and any config. -/
theorem qAvalanche_lt_two_pow (x : Nat) (q : QAvalancheConfig) : qAvalanche x q < 2 ^ 64 := by
  unfold qAvalanche
  have hmod : (x * q.mult) % (2 ^ 64) < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hshr : shr ((x * q.mult) % (2 ^ 64)) q.xor_shift < 2 ^ 64 := by
    have hle : shr ((x * q.mult) % (2 ^ 64)) q.xor_shift ≤ (x * q.mult) % (2 ^ 64) := by
      unfold shr; exact Nat.div_le_self _ _
    omega
  have hxor : ((x * q.mult) % (2 ^ 64) ^^^ shr ((x * q.mult) % (2 ^ 64)) q.xor_shift) < 2 ^ 64 :=
    xor_lt_two_pow _ _ 64 hmod hshr
  exact rotl64_lt_two_pow _ _ hxor

/-- `qAvalanche(x, cfg) ≠ 0` when `x ≠ 0`。
    由 qAvalanche_inj (b=0) + qAvalanche_zero 推导。
    需要 `invMult` (cfg.mult 的模 2^64 逆元) 和 `xor_shift ≥ 1`。 -/
theorem qAvalanche_ne_zero_of_ne_zero (x : Nat) (cfg : QAvalancheConfig) (invMult : Nat)
    (hx : x ≠ 0) (hx_lt : x < 2 ^ 64)
    (h_inv : (cfg.mult * invMult) % (2 ^ 64) = 1)
    (h_shift : 1 ≤ cfg.xor_shift) :
    qAvalanche x cfg ≠ 0 := by
  intro h_eq
  have h_zero : qAvalanche 0 cfg = 0 := qAvalanche_zero cfg
  have h_combined : qAvalanche x cfg = qAvalanche 0 cfg := by omega
  have h_eq := qAvalanche_inj x 0 cfg invMult h_combined hx_lt (by omega) h_inv h_shift
  exact hx h_eq