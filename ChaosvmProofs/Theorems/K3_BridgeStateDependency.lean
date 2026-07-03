import ChaosvmProofs.Definitions.SemShare
import ChaosvmProofs.Definitions.QAvalanche
import Init.Omega

set_option maxHeartbeats 50000000

open Nat

/-! # K3: Bridge Output Varies with State

The bridge output depends on the current state (σ, DDM) — it is not constant.
-/

namespace K3

/-- Pigeonhole principle for N+1 values all < N.

    If f maps {0..N} into {0..N-1} and is injective on {0..N},
    then we get a contradiction.  (N+1 > N, so two images must coincide.) -/
lemma no_inj_gt_range (f : ℕ → ℕ) (N : ℕ)
    (h_range : ∀ i, i < N + 1 → f i < N)
    (h_inj   : ∀ i j, i < N + 1 → j < N + 1 → f i = f j → i = j) : False := by
  induction' N with N IH generalizing f
  · -- N = 0: f(0) < 0 impossible
    have h0 : f 0 < 0 := h_range 0 (by omega)
    omega
  · -- N ≥ 0: f is injective on [0, N] with f(i) < N+1
    by_cases h_has_max : ∃ i, i < N + 1 ∧ f i = N
    · rcases h_has_max with ⟨i, hi, hfi⟩
      -- Remove index i by shifting: g(k) = f(k) for k < i, f(k+1) for k ≥ i
      let g := λ k => if k < i then f k else f (k + 1)
      have hg_range : ∀ k, k < N → g k < N := by
        intro k hk
        unfold g
        by_cases hk_i : k < i
        · have h_fk : f k < N + 1 := h_range k (by omega)
          have h_ne_N : f k ≠ N := by
            intro heq
            have := h_inj k i (by omega) hi (heq.trans hfi.symm)
            omega
          omega
        · have h_fk1 : f (k + 1) < N + 1 := h_range (k + 1) (by omega)
          have h_ne_N : f (k + 1) ≠ N := by
            intro heq
            have hk1_ne_i : k + 1 ≠ i := by omega
            have hk1_lt_Np1 : k + 1 < N + 1 := by omega
            have := h_inj (k + 1) i hk1_lt_Np1 hi (heq.trans hfi.symm)
            omega
          omega
      have hg_inj : ∀ k₁ k₂, k₁ < N → k₂ < N → g k₁ = g k₂ → k₁ = k₂ := by
        intro k₁ k₂ hk₁ hk₂ heq
        unfold g at heq
        by_cases hk₁_i : k₁ < i
        · by_cases hk₂_i : k₂ < i
          · -- both < i
            exact h_inj k₁ k₂ (by omega) (by omega) heq
          · -- k₁ < i ≤ k₂
            have := h_inj k₁ (k₂ + 1) (by omega) (by omega) (by omega)
            omega
        · by_cases hk₂_i : k₂ < i
          · -- k₂ < i ≤ k₁
            have := h_inj (k₁ + 1) k₂ (by omega) (by omega) (by omega)
            omega
          · -- both ≥ i
            have := h_inj (k₁ + 1) (k₂ + 1) (by omega) (by omega) heq
            omega
      exact IH g hg_range hg_inj
    · -- No f(i) = N, so all f(i) < N
      have h_range' : ∀ i, i < N + 1 → f i < N := by
        intro i hi
        have hfi : f i < N + 1 := h_range i hi
        have hfi_ne_N : f i ≠ N := by
          intro heq; apply h_has_max; exact ⟨i, hi, heq⟩
        omega
      exact IH f h_range' h_inj


/-- For any value v < 256 and any QAvalancheConfig with odd multiplier and
    xor_shift ≥ 1, there exists a state σ such that `permute v σ q ≠ v`.

    The proof encodes each qAvalanche output into `idx(σ) < 2^56`:
      idx = (2·a_idx + lo_bit)·2^48 + hi
    where a_idx = ((mix%256|1)-1)/2, lo_bit indicates if lo = a, hi = mix/65536.
    If every σ gave permute = v, then idx would be injective on [0, 2^56]
    with all values < 2^56, contradicting `no_inj_gt_range`. -/
lemma exists_sigma_permute_diff (v : ℕ) (hv : v < 256) (q : QAvalancheConfig) (invMult : ℕ)
    (h_inv : (q.mult * invMult) % 2 ^ 64 = 1) (h_shift : 1 ≤ q.xor_shift) :
    ∃ σ, permute v σ q ≠ v := by
  have h0 : qAvalanche 0 q = 0 := qAvalanche_zero q
  have hperm0 : permute v 0 q = v := by
    unfold permute; simp [h0, P_mod]
    calc (1 * v + 0) % 256 = v % 256 := by omega
      _ = v := Nat.mod_eq_of_lt hv
  have h_inj : ∀ a b, a < 2 ^ 64 → b < 2 ^ 64 → qAvalanche a q = qAvalanche b q → a = b :=
    λ a b ha hb h => qAvalanche_inj a b q invMult h ha hb h_inv h_shift

  by_contra! h_all
  -- h_all: ∀ σ, permute v σ q = v

  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- 1.  b(σ) = (qA(σ)/256)%256 determined by a(σ) = (qA%256|1)
  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  have h_b_det (σ : ℕ) : (qAvalanche σ q / 256) % 256 =
      (256 + v - (((qAvalanche σ q % 256 | 1) * v) % 256)) % 256 := by
    unfold permute at h_all
    have h := h_all σ
    unfold permute at h
    set a := (qAvalanche σ q % 256 | 1) with ha
    set b := (qAvalanche σ q / 256) % 256 with hb
    have ha_odd : a % 2 = 1 := by
      have h_all_lt256 : ∀ x < 256, (x | 1) % 2 = 1 := by decide
      exact h_all_lt256 (qAvalanche σ q % 256) (Nat.mod_lt _ (by decide : 0 < 256))
    omega

  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- 2.  Encoding: idx(σ) = (2·a_idx + lo_bit)·2^48 + hi  < 2^56
  --     where a = (mix%256|1), a_idx = (a-1)/2,
  --           lo_bit = 1 if mix%256 = a else 0,
  --           hi = mix / 65536.
  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  set mix := λ σ => qAvalanche σ q with hmix
  set a := λ σ => (mix σ % 256 | 1) with ha
  set lo := λ σ => mix σ % 256 with hlo
  set lo_bit := λ σ => if lo σ = a σ then 1 else 0 with hlo_bit
  set hi := λ σ => mix σ / 65536 with hhi
  set idx := λ σ => (((a σ - 1) / 2) * 2 + lo_bit σ) * 2 ^ 48 + hi σ with hidx

  have hmix_lt (σ : ℕ) : mix σ < 2 ^ 64 := by
    dsimp [mix]; unfold qAvalanche; apply rotl64_lt_two_pow

  have ha_range (σ : ℕ) : a σ < 256 := by
    dsimp [a]
    have h_mod_lt : mix σ % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
    have h_lor_lt : ∀ x < 256, (x | 1) < 256 := by decide
    exact h_lor_lt _ h_mod_lt

  have ha_odd (σ : ℕ) : a σ % 2 = 1 := by
    dsimp [a, mix]
    have h_all_lt256 : ∀ x < 256, (x | 1) % 2 = 1 := by decide
    exact h_all_lt256 (qAvalanche σ q % 256) (Nat.mod_lt _ (by decide : 0 < 256))

  have h_hi_lt (σ : ℕ) : hi σ < 2 ^ 48 := by
    dsimp [hi, mix]
    have h_mix_lt : qAvalanche σ q < 2 ^ 64 := hmix_lt σ
    have h_div_lt : qAvalanche σ q / 65536 < 2 ^ 64 / 65536 :=
      Nat.div_lt_of_lt_mul h_mix_lt
    calc
      qAvalanche σ q / 65536 < 2 ^ 64 / 65536 := h_div_lt
      _ = 2 ^ 48 := by norm_num

  have h_idx_lt_2pow56 (σ : ℕ) : idx σ < 2 ^ 56 := by
    unfold idx
    have ha_val_le : ((a σ - 1) / 2) * 2 + lo_bit σ ≤ 255 := by
      have ha_le : a σ ≤ 255 := by omega
      have h_lo_bit_le : lo_bit σ ≤ 1 := by
        unfold lo_bit; split <;> omega
      omega
    have h_hi_lt_48 : hi σ < 2 ^ 48 := h_hi_lt σ
    calc
      (((a σ - 1) / 2) * 2 + lo_bit σ) * 2 ^ 48 + hi σ
          ≤ 255 * 2 ^ 48 + (2 ^ 48 - 1) := by
            have hval : ((a σ - 1) / 2) * 2 + lo_bit σ ≤ 255 := ha_val_le
            have hhi_le : hi σ ≤ 2 ^ 48 - 1 := by omega
            omega
      _ = 256 * 2 ^ 48 - 1 := by omega
      _ = 2 ^ 56 - 1 := by norm_num
      _ < 2 ^ 56 := by omega

  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- 3.  idx is injective on [0, 2^56] under h_all
  --     (idx(i) = idx(j) ⇒ qAvalanche(i) = qAvalanche(j) ⇒ i=j)
  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  have h_idx_inj : ∀ i j, i < 2 ^ 56 + 1 → j < 2 ^ 56 + 1 → idx i = idx j → i = j := by
    intro i j hi hj hidx_eq
    unfold idx at hidx_eq

    -- Step 1: from idx equality, extract hi and (a-1)/2*2+lo_bit
    have h_hi_i_lt : hi i < 2 ^ 48 := h_hi_lt i
    have h_hi_j_lt : hi j < 2 ^ 48 := h_hi_lt j

    have h_mod_eq : hi i = hi j := by
      calc
        hi i = ((((a i - 1) / 2) * 2 + lo_bit i) * 2 ^ 48 + hi i) % 2 ^ 48 := by
          simp [h_hi_i_lt]
        _ = ((((a j - 1) / 2) * 2 + lo_bit j) * 2 ^ 48 + hi j) % 2 ^ 48 := by rw [hidx_eq]
        _ = hi j := by simp [h_hi_j_lt]

    have h_val_eq : ((a i - 1) / 2) * 2 + lo_bit i = ((a j - 1) / 2) * 2 + lo_bit j := by
      have h_mul_eq : (((a i - 1) / 2) * 2 + lo_bit i) * 2 ^ 48 = (((a j - 1) / 2) * 2 + lo_bit j) * 2 ^ 48 := by
        omega
      have hpos : 2 ^ 48 > 0 := by norm_num
      exact (Nat.eq_of_mul_eq_mul_left hpos h_mul_eq)

    -- Step 2: from (a-1)/2*2+lo_bit equality, extract a and lo_bit
    have h_lo_bit_eq : lo_bit i = lo_bit j := by
      calc
        lo_bit i = (((a i - 1) / 2) * 2 + lo_bit i) % 2 := by
          have h_val_mod : (((a i - 1) / 2) * 2 + lo_bit i) % 2 = lo_bit i := by
            have h_even : ((a i - 1) / 2) * 2 % 2 = 0 := by simp
            have h_lo_bit_le1 : lo_bit i < 2 := by
              unfold lo_bit; split <;> omega
            omega
          calc
            lo_bit i = lo_bit i := rfl
            _ = (((a i - 1) / 2) * 2 + lo_bit i) % 2 := by
              symm
              apply Nat.mod_eq_of_lt
              unfold lo_bit; split <;> omega
        _ = (((a j - 1) / 2) * 2 + lo_bit j) % 2 := by rw [h_val_eq]
        _ = lo_bit j := by
          have h_even : ((a j - 1) / 2) * 2 % 2 = 0 := by simp
          have h_lo_bit_le1 : lo_bit j < 2 := by
            unfold lo_bit; split <;> omega
          omega

    have ha_idx_eq : (a i - 1) / 2 = (a j - 1) / 2 := by
      have h_mul : ((a i - 1) / 2) * 2 = ((a j - 1) / 2) * 2 := by
        omega
      apply (Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)) h_mul

    have ha_eq : a i = a j := by
      have ha_i_odd : a i % 2 = 1 := ha_odd i
      have ha_j_odd : a j % 2 = 1 := ha_odd j
      omega

    -- Step 3: reconstruct qAvalanche values
    have h_b_eq (σ : ℕ) : (mix σ / 256) % 256 = (256 + v - ((a σ * v) % 256)) % 256 := by
      calc
        (mix σ / 256) % 256 = (qAvalanche σ q / 256) % 256 := rfl
        _ = (256 + v - (((qAvalanche σ q % 256 | 1) * v) % 256)) % 256 := h_b_det σ
        _ = (256 + v - ((a σ * v) % 256)) % 256 := rfl

    have h_lo_eq : lo i = lo j := by
      unfold lo lo_bit at h_lo_bit_eq
      have h_lo_i : (mix i % 256) = a i ∨ (mix i % 256) = a i - 1 := by
        have ha_i_odd : a i % 2 = 1 := ha_odd i
        have h_lor : (mix i % 256 | 1) = a i := rfl
        have h_lo_lt_256 : mix i % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
        -- (mix%256 | 1) = a i, an odd number < 256
        -- The only x < 256 with (x|1) = a i are x = a i and x = a i - 1
        have h_poss : (∀ x < 256, (x | 1) = a i → x = a i ∨ x = a i - 1) := by
          decide
        exact h_poss (mix i % 256) h_lo_lt_256 h_lor
      have h_lo_j : (mix j % 256) = a j ∨ (mix j % 256) = a j - 1 := by
        have ha_j_odd : a j % 2 = 1 := ha_odd j
        have h_lor_j : (mix j % 256 | 1) = a j := rfl
        have h_lo_lt_256 : mix j % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
        have h_poss : (∀ x < 256, (x | 1) = a j → x = a j ∨ x = a j - 1) := by
          decide
        exact h_poss (mix j % 256) h_lo_lt_256 h_lor_j

      -- Based on lo_bit value, determine lo
      rcases h_lo_i with (h_i_a | h_i_a1)
      · rcases h_lo_j with (h_j_a | h_j_a1)
        · calc
            lo i = mix i % 256 := rfl
            _ = a i := h_i_a
            _ = a j := ha_eq
            _ = mix j % 256 := h_j_a.symm
            _ = lo j := rfl
        · have : lo_bit i = 1 := by
            unfold lo_bit; simp [h_i_a]
          have : lo_bit j = 0 := by
            unfold lo_bit; simp [h_j_a1, ha_eq]
          rw [this] at h_lo_bit_eq; omega
      · rcases h_lo_j with (h_j_a | h_j_a1)
        · have : lo_bit i = 0 := by
            unfold lo_bit; simp [h_i_a1]
          have : lo_bit j = 1 := by
            unfold lo_bit; simp [h_j_a, ha_eq]
          rw [this] at h_lo_bit_eq; omega
        · calc
            lo i = mix i % 256 := rfl
            _ = a i - 1 := h_i_a1
            _ = a j - 1 := by rw [ha_eq]
            _ = mix j % 256 := h_j_a1.symm
            _ = lo j := rfl

    have h_b_i_val : (mix i / 256) % 256 = (256 + v - ((a i * v) % 256)) % 256 := h_b_eq i
    have h_b_j_val : (mix j / 256) % 256 = (256 + v - ((a j * v) % 256)) % 256 := h_b_eq j

    have h_b_eq_val : (mix i / 256) % 256 = (mix j / 256) % 256 := by
      calc
        (mix i / 256) % 256 = (256 + v - ((a i * v) % 256)) % 256 := h_b_i_val
        _ = (256 + v - ((a j * v) % 256)) % 256 := by rw [ha_eq]
        _ = (mix j / 256) % 256 := h_b_j_val.symm

    -- Reconstruct: mix = hi·65536 + (mix/256%256)·256 + (mix%256)
    have hmix_i_val : mix i = hi i * 65536 + ((mix i / 256) % 256) * 256 + (mix i % 256) := by
      have h := Nat.div_add_mod (mix i) 256
      have h' : mix i = (mix i / 256) * 256 + mix i % 256 := h
      calc
        mix i = (mix i / 256) * 256 + mix i % 256 := h'
        _ = ((mix i / 256 / 256) * 256 + (mix i / 256) % 256) * 256 + mix i % 256 := by
          have h2 := Nat.div_add_mod (mix i / 256) 256
          omega
        _ = (mix i / 65536) * 65536 + ((mix i / 256) % 256) * 256 + mix i % 256 := by ring
        _ = hi i * 65536 + ((mix i / 256) % 256) * 256 + mix i % 256 := rfl
    
    have hmix_j_val : mix j = hi j * 65536 + ((mix j / 256) % 256) * 256 + (mix j % 256) := by
      have h := Nat.div_add_mod (mix j) 256
      have h' : mix j = (mix j / 256) * 256 + mix j % 256 := h
      calc
        mix j = (mix j / 256) * 256 + mix j % 256 := h'
        _ = ((mix j / 256 / 256) * 256 + (mix j / 256) % 256) * 256 + mix j % 256 := by
          have h2 := Nat.div_add_mod (mix j / 256) 256
          omega
        _ = (mix j / 65536) * 65536 + ((mix j / 256) % 256) * 256 + mix j % 256 := by ring
        _ = hi j * 65536 + ((mix j / 256) % 256) * 256 + mix j % 256 := rfl

    have hmix_eq : mix i = mix j := by
      calc
        mix i = hi i * 65536 + ((mix i / 256) % 256) * 256 + (mix i % 256) := hmix_i_val
        _ = hi j * 65536 + ((mix j / 256) % 256) * 256 + (mix j % 256) := by
          rw [h_mod_eq, h_b_eq_val, h_lo_eq]
        _ = mix j := hmix_j_val.symm

    -- Step 4: apply qAvalanche_inj to conclude i = j
    have hi_lt_64 : i < 2 ^ 64 := by
      have h : 2 ^ 56 + 1 ≤ 2 ^ 64 := by norm_num
      omega
    have hj_lt_64 : j < 2 ^ 64 := by
      have h : 2 ^ 56 + 1 ≤ 2 ^ 64 := by norm_num
      omega
    exact h_inj i j hi_lt_64 hj_lt_64 hmix_eq

  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- 4.  Contractiction: idx is < 2^56 and injective on [0, 2^56], impossible
  --━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  have h_range : ∀ i, i < 2 ^ 56 + 1 → idx i < 2 ^ 56 :=
    λ i hi => h_idx_lt_2pow56 i

  exact no_inj_gt_range idx (2 ^ 56) h_range h_idx_inj


/-- K3: Bridge output varies with state.

    For any `c0, anchor, c1_t, c2` and any QAvalancheConfig with odd multiplier
    and xor_shift ≥ 1, there exist `(σ₁,σ₂,DDM₁,DDM₂)` giving different bridge outputs. -/
theorem K3_bridge_varies_with_state (c0 anchor c1_t c2 : ℕ) (q : QAvalancheConfig) (invMult : ℕ)
    (h_inv : (q.mult * invMult) % 2 ^ 64 = 1) (h_shift : 1 ≤ q.xor_shift) :
    ∃ (σ₁ σ₂ DDM₁ DDM₂ : ℕ), bridge_i41 c0 anchor c1_t c2 σ₁ DDM₁ q q ≠
                             bridge_i41 c0 anchor c1_t c2 σ₂ DDM₂ q q := by
  have h0 : qAvalanche 0 q = 0 := qAvalanche_zero q
  have hperm0 (x : ℕ) : permute x 0 q = x % 256 := by
    unfold permute; simp [h0, P_mod]
    calc (1 * x + 0) % 256 = x % 256 := by omega
      _ = x % 256 := rfl

  set v := c1_t % 256 with hv
  have hv_lt : v < 256 := Nat.mod_lt _ (by decide : 0 < 256)

  by_cases h_diff : ∃ σ₂, permute c1_t σ₂ q ≠ c1_t % 256
  · rcases h_diff with ⟨σ₂, hσ₂⟩
    refine ⟨0, σ₂, 0, 0, ?_⟩
    unfold bridge_i41
    have h_perm0 : permute c1_t 0 q = c1_t % 256 := hperm0 c1_t
    have h_cancel0 : permute c2 0 q ^^^ permute c2 0 q = 0 := Nat.xor_self _
    calc
      c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q ^^^ permute c2 0 q ^^^ permute c2 0 q
          = c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q := by
            simp [h_cancel0]
      _ ≠ c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := by
        intro h_eq
        apply hσ₂
        have : permute c1_t σ₂ q = c1_t % 256 := by
          -- from the bridge equality, XOR cancel common terms
          have h_all : c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := h_eq
          have h_core : permute c1_t σ₂ q = c1_t % 256 := by
            calc
              permute c1_t σ₂ q = c0 ^^^ (c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q) ^^^ permute anchor 0 q := by
                simp [Nat.xor_assoc]
              _ = c0 ^^^ (c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q) ^^^ permute anchor 0 q := by rw [h_all]
              _ = c1_t % 256 := by simp [Nat.xor_assoc]
          exact h_core
        exact hσ₂ this
      _ = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := rfl
    -- simplify: show bridge_1 ≠ bridge_0
    calc
      c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q
          ≠ c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := by
            intro h_eq
            apply hσ₂
            calc
              permute c1_t σ₂ q = c0 ^^^ (c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q) ^^^ permute anchor 0 q := by
                simp [Nat.xor_assoc]
              _ = c0 ^^^ (c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q) ^^^ permute anchor 0 q := by rw [h_eq]
              _ = c1_t % 256 := by simp [Nat.xor_assoc]
      _ = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := rfl
  · -- h_diff: ∀ σ₂, permute c1_t σ₂ q = c1_t % 256
    by_cases h_diff' : ∃ DDM₂, permute c2 DDM₂ q ≠ c2 % 256
    · rcases h_diff' with ⟨DDM₂, hDDM₂⟩
      refine ⟨0, 0, 0, DDM₂, ?_⟩
      unfold bridge_i41
      have h_perm0_c1 : permute c1_t 0 q = c1_t % 256 := hperm0 c1_t
      have h_perm0_c2 : permute c2 0 q = c2 % 256 := hperm0 c2
      have h_cancel0 : permute c2 DDM₂ q ^^^ permute c2 0 q ≠ c2 % 256 ^^^ c2 % 256 := by
        intro h_eq
        apply hDDM₂
        calc
          permute c2 DDM₂ q = permute c2 DDM₂ q ^^^ 0 := by simp
          _ = permute c2 DDM₂ q ^^^ (c2 % 256 ^^^ c2 % 256) := by simp
          _ = (permute c2 DDM₂ q ^^^ c2 % 256) ^^^ c2 % 256 := by simp [Nat.xor_assoc]
          _ = (permute c2 DDM₂ q ^^^ permute c2 0 q) ^^^ c2 % 256 := by rw [h_perm0_c2]
          _ = (c2 % 256 ^^^ c2 % 256) ^^^ c2 % 256 := by rw [h_eq]
          _ = c2 % 256 := by simp
      -- The main inequality
      calc
        c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ permute c2 DDM₂ q ^^^ (c2 % 256)
            = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ (permute c2 DDM₂ q ^^^ (c2 % 256)) := by
              simp [Nat.xor_assoc]
        _ = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ 0 ^^^ (permute c2 DDM₂ q ^^^ (c2 % 256)) := by simp
        _ ≠ c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ (c2 % 256 ^^^ (c2 % 256)) := by
          -- This is where the inequality matters
          intro h_eq
          have : permute c2 DDM₂ q ^^^ (c2 % 256) = (c2 % 256) ^^^ (c2 % 256) := by
            apply (Nat.xor_left_cancel (c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q)).mp
            simpa [Nat.xor_assoc] using h_eq
          apply h_cancel0
          simpa using this
        _ = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := by simp
    · -- h_diff': ∀ DDM₂, permute c2 DDM₂ q = c2 % 256
      -- This case should also be impossible under our assumptions
      -- Since both permutes are identity, we use the lemma to find a contradiction
      exfalso
      have h_exists : ∃ σ, permute (c1_t % 256) σ q ≠ c1_t % 256 :=
        exists_sigma_permute_diff (c1_t % 256) (by
          apply Nat.mod_lt _ (by decide : 0 < 256)) q invMult h_inv h_shift
      rcases h_exists with ⟨σ, hσ⟩
      apply hσ
      apply h_diff σ
