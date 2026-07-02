import ChaosvmProofs.Definitions.StateUpdate
import ChaosvmProofs.Definitions.Helpers



/-! # K2: H 链顺序依赖 (H Chain Dependency)

## Theorems

- *K2b_ra*: `digest_operands(ra, rb)` determines `ra` uniquely given `rb`.
- *K2b_rb*: `digest_operands(ra, rb)` determines `rb` uniquely given `ra`.

These replace the original K2b (`digest_operands` injective on (ra,rb)) which
is false due to XOR composition: `ra*C ⊕ rotl(rb,13)` loses pair information.
Each individual operand IS recoverable when the other is known.

## Proof Strategy

K2b_ra: `digest ⊕ rotl(rb,13) = ra*C mod 2^64`. Since C is odd, `ra ↦ ra*C mod 2^64`
is injective on [0, 2^64-1] (modular inverse exists). Pre-computed `invC` verified
by `native_decide`.

K2b_rb: `digest ⊕ (ra*C mod 2^64) = rotl(rb,13)`. Since `rotl64(·,13)` is injective
on [0, 2^64-1] (left inverse `rotr64` recovers `rb`), `rb` is uniquely determined.
The identity is proved via `omega` on a decomposed rotation.
-/

/-- XOR left cancellation: `a ⊕ b = a ⊕ c` implies `b = c`. -/
theorem xor_left_cancel (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  calc
    b = (a ^^^ a) ^^^ b := by simp
    _ = a ^^^ (a ^^^ b) := by rw [Nat.xor_assoc]
    _ = a ^^^ (a ^^^ c) := by rw [h]
    _ = (a ^^^ a) ^^^ c := by rw [Nat.xor_assoc]
    _ = c := by simp

/-- The golden ratio constant used in `digest_operands`. -/
def C : Nat := 0x9e3779b97f4a7c15

/-- Modular inverse of C modulo 2^64: C * invC ≡ 1 (mod 2^64). -/
def invC : Nat := 0xf1de83e19937733d

/-- Verified: `(C * invC) % 2^64 = 1`. -/
theorem C_mul_invC_mod_eq_one : (C * invC) % (2 ^ 64) = 1 := by
  native_decide

/-- `mul_C_inj_mod_2pow64`: Multiplication by odd C is injective modulo 2^64
    for values < 2^64.

    If `(a*C) % 2^64 = (b*C) % 2^64` and `a,b < 2^64`, then `a = b`. -/
theorem mul_C_inj_mod_2pow64 (a b : Nat) (h : (a * C) % (2 ^ 64) = (b * C) % (2 ^ 64))
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a = b := by
  have h_inv : (C * invC) % (2 ^ 64) = 1 := C_mul_invC_mod_eq_one
  have ha_val : a % (2 ^ 64) = a := Nat.mod_eq_of_lt ha
  have hb_val : b % (2 ^ 64) = b := Nat.mod_eq_of_lt hb
  -- Lemma: (x % 2^64 * invC) % 2^64 = (x * invC) % 2^64
  have h_mod_mul (x : Nat) : (x % (2 ^ 64) * invC) % (2 ^ 64) = (x * invC) % (2 ^ 64) := by
    calc
      (x % (2 ^ 64) * invC) % (2 ^ 64) = ((x % (2 ^ 64)) % (2 ^ 64) * (invC % (2 ^ 64))) % (2 ^ 64) := by
        rw [Nat.mul_mod]
      _ = (x % (2 ^ 64) * (invC % (2 ^ 64))) % (2 ^ 64) := by rw [Nat.mod_mod]
      _ = (x * invC) % (2 ^ 64) := by rw [← Nat.mul_mod]
  have ha_restore : (a * C) % (2 ^ 64) * invC % (2 ^ 64) = a := by
    calc
      (a * C) % (2 ^ 64) * invC % (2 ^ 64) = (a * C * invC) % (2 ^ 64) := by
        rw [h_mod_mul (a * C)]
      _ = (a * (C * invC)) % (2 ^ 64) := by rw [Nat.mul_assoc]
      _ = ((a % (2 ^ 64)) * ((C * invC) % (2 ^ 64))) % (2 ^ 64) := by rw [Nat.mul_mod]
      _ = (a * ((C * invC) % (2 ^ 64))) % (2 ^ 64) := by rw [ha_val]
      _ = (a * 1) % (2 ^ 64) := by rw [h_inv]
      _ = a % (2 ^ 64) := by omega
      _ = a := ha_val
  have hb_restore : (b * C) % (2 ^ 64) * invC % (2 ^ 64) = b := by
    calc
      (b * C) % (2 ^ 64) * invC % (2 ^ 64) = (b * C * invC) % (2 ^ 64) := by
        rw [h_mod_mul (b * C)]
      _ = (b * (C * invC)) % (2 ^ 64) := by rw [Nat.mul_assoc]
      _ = ((b % (2 ^ 64)) * ((C * invC) % (2 ^ 64))) % (2 ^ 64) := by rw [Nat.mul_mod]
      _ = (b * ((C * invC) % (2 ^ 64))) % (2 ^ 64) := by rw [hb_val]
      _ = (b * 1) % (2 ^ 64) := by rw [h_inv]
      _ = b % (2 ^ 64) := by omega
      _ = b := hb_val
  calc
    a = (a * C) % (2 ^ 64) * invC % (2 ^ 64) := by rw [ha_restore]
    _ = (b * C) % (2 ^ 64) * invC % (2 ^ 64) := by rw [h]
    _ = b := by rw [hb_restore]

/-- Simple rotation by 13, matching `rotl64` for x < 2^64: `(x % 2^51)*2^13 + x/2^51`. -/
def simple_rotl (x : Nat) : Nat :=
  (x % (2 ^ 51)) * (2 ^ 13) + x / (2 ^ 51)

/-- Simple inverse rotation by 13, matching `rotr64` for y < 2^64. -/
def simple_rotr (y : Nat) : Nat :=
  y / (2 ^ 13) + (y % (2 ^ 13)) * (2 ^ 51)

/-- `rotl64` equals `simple_rotl` for x < 2^64. -/
theorem rotl64_eq_simple_rotl (x : Nat) (hx : x < 2 ^ 64) : rotl64 x 13 = simple_rotl x := by
  unfold rotl64 simple_rotl shl shr mask64
  simp
  have h_hi : x / 2 ^ 51 < 2 ^ 13 := by
    apply Nat.div_lt_of_lt_mul; omega
  have h_hi_lt_64 : x / 2 ^ 51 < 2 ^ 64 := by
    apply Nat.lt_of_lt_of_le h_hi
    refine Nat.pow_le_pow_right (by omega) (by omega)
  have h_lo : x % 2 ^ 51 < 2 ^ 51 := Nat.mod_lt _ (by decide : 0 < 2 ^ 51)
  have h_pow : 2 ^ 51 * 2 ^ 13 = 2 ^ 64 := by
    calc
      2 ^ 51 * 2 ^ 13 = 2 ^ (51 + 13) := by rw [Nat.pow_add]
      _ = 2 ^ 64 := by omega
  have h_mul_lt : (x % 2 ^ 51) * 2 ^ 13 < 2 ^ 64 := by
    have h_lt_mul : (x % 2 ^ 51) * 2 ^ 13 < 2 ^ 51 * 2 ^ 13 :=
      Nat.mul_lt_mul_of_pos_right h_lo (by decide : 0 < 2 ^ 13)
    omega
  have h_shl_mod : (x * 2 ^ 13) % 2 ^ 64 = (x % 2 ^ 51) * 2 ^ 13 := by
    have hx_decomp : x = (x % 2 ^ 51) + 2 ^ 51 * (x / 2 ^ 51) := by omega
    have h_x_times_pow : x * 2 ^ 13 = (x % 2 ^ 51) * 2 ^ 13 + (x / 2 ^ 51) * 2 ^ 64 := by
      calc
        x * 2 ^ 13 = ((x % 2 ^ 51) + 2 ^ 51 * (x / 2 ^ 51)) * 2 ^ 13 := by
          simpa using congrArg (· * 2 ^ 13) hx_decomp
        _ = (x % 2 ^ 51) * 2 ^ 13 + (2 ^ 51 * (x / 2 ^ 51)) * 2 ^ 13 := by rw [Nat.add_mul]
        _ = (x % 2 ^ 51) * 2 ^ 13 + (x / 2 ^ 51) * (2 ^ 51 * 2 ^ 13) := by
          omega
        _ = (x % 2 ^ 51) * 2 ^ 13 + (x / 2 ^ 51) * 2 ^ 64 := by rw [h_pow]
    calc
      (x * 2 ^ 13) % 2 ^ 64 = ((x % 2 ^ 51) * 2 ^ 13 + (x / 2 ^ 51) * 2 ^ 64) % 2 ^ 64 := by rw [h_x_times_pow]
      _ = ((x % 2 ^ 51) * 2 ^ 13) % 2 ^ 64 := by
        calc
          ((x % 2 ^ 51) * 2 ^ 13 + (x / 2 ^ 51) * 2 ^ 64) % 2 ^ 64 =
            (((x % 2 ^ 51) * 2 ^ 13) % 2 ^ 64 + ((x / 2 ^ 51) * 2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by rw [Nat.add_mod]
          _ = (((x % 2 ^ 51) * 2 ^ 13) % 2 ^ 64 + 0) % 2 ^ 64 := by simp
          _ = ((x % 2 ^ 51) * 2 ^ 13) % 2 ^ 64 := by simp
      _ = (x % 2 ^ 51) * 2 ^ 13 := Nat.mod_eq_of_lt h_mul_lt
  have h_mask : (x / 2 ^ 51) &&& (2 ^ 64 - 1) = x / 2 ^ 51 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h_hi_lt_64]
  have h_lor_eq : (x % 2 ^ 51) * 2 ^ 13 ||| (x / 2 ^ 51) = (x % 2 ^ 51) * 2 ^ 13 + x / 2 ^ 51 := by
    calc
      (x % 2 ^ 51) * 2 ^ 13 ||| (x / 2 ^ 51) = 2 ^ 13 * (x % 2 ^ 51) ||| (x / 2 ^ 51) := by rw [Nat.mul_comm]
      _ = 2 ^ 13 * (x % 2 ^ 51) + (x / 2 ^ 51) :=
        (Nat.two_pow_add_eq_or_of_lt h_hi (x % 2 ^ 51)).symm
      _ = (x % 2 ^ 51) * 2 ^ 13 + x / 2 ^ 51 := by rw [Nat.mul_comm]
  rw [h_shl_mod, h_mask, ← h_lor_eq]

/-- `simple_rotl` and `simple_rotr` are inverses for x < 2^64. -/
theorem simple_rotl_rotr_inverse (x : Nat) (hx : x < 2 ^ 64) : simple_rotr (simple_rotl x) = x := by
  unfold simple_rotl simple_rotr; omega

/-- `rotl13_injective`: `rotl64(·, 13)` is injective on `[0, 2^64-1]`. -/
theorem rotl13_injective (a b : Nat) (h : rotl64 a 13 = rotl64 b 13)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a = b := by
  have h_simple : simple_rotl a = simple_rotl b := by
    calc
      simple_rotl a = rotl64 a 13 := by symm; exact rotl64_eq_simple_rotl a ha
      _ = rotl64 b 13 := h
      _ = simple_rotl b := rotl64_eq_simple_rotl b hb
  calc
    a = simple_rotr (simple_rotl a) := by rw [simple_rotl_rotr_inverse a ha]
    _ = simple_rotr (simple_rotl b) := by rw [h_simple]
    _ = b := by rw [simple_rotl_rotr_inverse b hb]

/-- `digest_operands_ra_injective`: Given `digest_operands(ra1, rb) = digest_operands(ra2, rb)`,
    and `ra1, ra2 < 2^64`, then `ra1 = ra2`. -/
theorem digest_operands_ra_injective (ra1 ra2 rb : Nat)
    (h : digest_operands ra1 rb = digest_operands ra2 rb)
    (hra1 : ra1 < 2 ^ 64) (hra2 : ra2 < 2 ^ 64) : ra1 = ra2 := by
  unfold digest_operands at h
  have h_mul : (ra1 * C) % (2 ^ 64) = (ra2 * C) % (2 ^ 64) := by
    apply xor_left_cancel (rotl64 rb 13) ((ra1 * C) % (2 ^ 64)) ((ra2 * C) % (2 ^ 64))
    simpa [Nat.xor_comm] using h
  exact mul_C_inj_mod_2pow64 ra1 ra2 h_mul hra1 hra2

/-- `digest_operands_rb_injective`: Given `digest_operands(ra, rb1) = digest_operands(ra, rb2)`,
    and `rb1, rb2 < 2^64`, then `rb1 = rb2`. -/
theorem digest_operands_rb_injective (ra rb1 rb2 : Nat)
    (h : digest_operands ra rb1 = digest_operands ra rb2)
    (hrb1 : rb1 < 2 ^ 64) (hrb2 : rb2 < 2 ^ 64) : rb1 = rb2 := by
  unfold digest_operands at h
  have h_rotl : rotl64 rb1 13 = rotl64 rb2 13 := by
    apply xor_left_cancel ((ra * C) % (2 ^ 64)) (rotl64 rb1 13) (rotl64 rb2 13)
    simpa using h
  exact rotl13_injective rb1 rb2 h_rotl hrb1 hrb2
