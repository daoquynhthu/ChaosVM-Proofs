import ChaosvmProofs.Definitions.SemShare
import ChaosvmProofs.Definitions.QAvalanche
import Init.Omega

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

open Nat

theorem xor_left_cancel (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  calc
    b = (a ^^^ a) ^^^ b := by simp
    _ = a ^^^ (a ^^^ b) := by rw [Nat.xor_assoc]
    _ = a ^^^ (a ^^^ c) := by rw [h]
    _ = (a ^^^ a) ^^^ c := by rw [Nat.xor_assoc]
    _ = c := by simp

theorem xor_quad_cancel (c a b : Nat) : c ^^^ (c ^^^ a ^^^ b) ^^^ b = a := by
  calc
    c ^^^ (c ^^^ a ^^^ b) ^^^ b = (c ^^^ ((c ^^^ a) ^^^ b)) ^^^ b := rfl
    _ = ((c ^^^ (c ^^^ a)) ^^^ b) ^^^ b := by rw [← Nat.xor_assoc]
    _ = (((c ^^^ c) ^^^ a) ^^^ b) ^^^ b := by rw [← Nat.xor_assoc]
    _ = ((0 ^^^ a) ^^^ b) ^^^ b := by simp
    _ = (a ^^^ b) ^^^ b := by simp
    _ = a ^^^ (b ^^^ b) := by rw [Nat.xor_assoc]
    _ = a ^^^ 0 := by simp
    _ = a := by simp

/-! # K3: Bridge Output Varies with State

The bridge output depends on the current state (σ, DDM) — it is not constant.
-/

namespace K3

/-- Pigeonhole principle for N+1 values all < N.

    If f maps {0..N} into {0..N-1} and is injective on {0..N},
    then we get a contradiction.  (N+1 > N, so two images must coincide.) -/
theorem no_inj_gt_range (f : Nat → Nat) (N : Nat)
    (h_range : ∀ i, i < N + 1 → f i < N)
    (h_inj   : ∀ i j, i < N + 1 → j < N + 1 → f i = f j → i = j) : False := by
  induction N generalizing f with
  | zero =>
    have h0 : f 0 < 0 := h_range 0 (by omega)
    omega
  | succ m IH =>
    by_cases h_has_max : ∃ i, i < m + 1 + 1 ∧ f i = m
    · rcases h_has_max with ⟨i, hi, hfi⟩
      let g := λ k => if k < i then f k else f (k + 1)
      have hg_range : ∀ k, k < m + 1 → g k < m := by
        intro k hk
        unfold g
        by_cases hk_i : k < i
        · have h_fk : f k < m + 1 := h_range k (by omega)
          have h_ne_N : f k ≠ m := by
            intro heq
            have hki : k = i := h_inj k i (by omega) hi (heq.trans hfi.symm)
            rw [hki] at hk_i
            omega
          have h_fk_lt_m : f k < m := by
            have hle : f k ≤ m := Nat.lt_succ_iff.mp h_fk
            rcases Nat.lt_or_eq_of_le hle with (h | h)
            · exact h
            · exact absurd h h_ne_N
          simpa [hk_i] using h_fk_lt_m
        · have h_fk1 : f (k + 1) < m + 1 := h_range (k + 1) (by omega)
          have h_ne_N : f (k + 1) ≠ m := by
            intro heq
            have hki : k + 1 = i := h_inj (k + 1) i (by omega) hi (heq.trans hfi.symm)
            have : i ≤ k := Nat.le_of_not_gt hk_i
            have : k + 1 ≤ k := by simpa [hki] using this
            exact Nat.not_succ_le_self k this
          have h_fk1_lt_m : f (k + 1) < m := by
            have hle : f (k + 1) ≤ m := Nat.lt_succ_iff.mp h_fk1
            rcases Nat.lt_or_eq_of_le hle with (h | h)
            · exact h
            · exact absurd h h_ne_N
          simpa [hk_i] using h_fk1_lt_m
      have hg_inj : ∀ k₁ k₂, k₁ < m + 1 → k₂ < m + 1 → g k₁ = g k₂ → k₁ = k₂ := by
        intro k₁ k₂ hk₁ hk₂ heq
        unfold g at heq
        by_cases hk₁_i : k₁ < i
        · by_cases hk₂_i : k₂ < i
          · exact h_inj k₁ k₂ (by omega) (by omega) (by simpa [hk₁_i, hk₂_i] using heq)
          · have h_eq : f k₁ = f (k₂ + 1) := by
              simpa [hk₁_i, hk₂_i] using heq
            have := h_inj k₁ (k₂ + 1) (by omega) (by omega) h_eq
            omega
        · by_cases hk₂_i : k₂ < i
          · have h_eq : f (k₁ + 1) = f k₂ := by
              simpa [hk₁_i, hk₂_i] using heq
            have := h_inj (k₁ + 1) k₂ (by omega) (by omega) h_eq
            omega
          · have h_eq : f (k₁ + 1) = f (k₂ + 1) := by
              simpa [hk₁_i, hk₂_i] using heq
            exact Nat.succ_inj.mp (h_inj (k₁ + 1) (k₂ + 1) (by omega) (by omega) h_eq)
      exact IH g hg_range hg_inj
    · have h_range' : ∀ i, i < m + 1 → f i < m := by
        intro i hi
        have hfi : f i < m + 1 := h_range i (by omega)
        have hfi_ne_N : f i ≠ m := by
          intro heq; apply h_has_max; exact ⟨i, by omega, heq⟩
        omega
      have h_inj' : ∀ i j, i < m + 1 → j < m + 1 → f i = f j → i = j := by
        intro i j hi hj
        apply h_inj i j (by omega) (by omega)
      exact IH f h_range' h_inj'


/-- For any value v < 256 and any QAvalancheConfig with odd multiplier and
    xor_shift ≥ 1, there exists a state σ such that `permute v σ q ≠ v`.

    The proof encodes each qAvalanche output into `idx(σ) < 2^56`:
      idx = (2·a_idx + lo_bit)·2^48 + hi
    where a_idx = ((mix%256|1)-1)/2, lo_bit indicates if lo = a, hi = mix/65536.
    If every σ gave permute = v, then idx would be injective on [0, 2^56]
    with all values < 2^56, contradicting `no_inj_gt_range`. -/
theorem exists_sigma_permute_diff (v : Nat) (hv : v < 256) (q : QAvalancheConfig) (invMult : Nat)
    (h_inv : (q.mult * invMult) % 2 ^ 64 = 1) (h_shift : 1 ≤ q.xor_shift) :
    ∃ σ, permute v σ q ≠ v := by
  have h0 : qAvalanche 0 q = 0 := qAvalanche_zero q
  have hperm0 : permute v 0 q = v := by
    dsimp [permute, P_mod]
    simp [h0]
    omega
  have h_inj : ∀ a b, a < 2 ^ 64 → b < 2 ^ 64 → qAvalanche a q = qAvalanche b q → a = b :=
    λ a b ha hb h => qAvalanche_inj a b q invMult h ha hb h_inv h_shift

  by_cases h_all' : ∃ σ, permute v σ q ≠ v
  · exact h_all'
  · exfalso
    have h_all : ∀ σ, permute v σ q = v := by
      intro σ
      by_cases h : permute v σ q = v
      · exact h
      · exfalso
        exact h_all' ⟨σ, h⟩
    have h_contra : False := by
      have h_b_det (σ : Nat) : (qAvalanche σ q / 256) % 256 =
          (256 + v - ((Nat.lor (qAvalanche σ q % 256) 1 * v) % 256)) % 256 := by
        have h_av_b_mod256 : (Nat.lor (qAvalanche σ q % 256) 1 * v + (qAvalanche σ q / 256) % 256) % 256 = v :=
          Eq.trans ((permute_eq_mod_form v σ q).symm) (h_all σ)
        let a := Nat.lor (qAvalanche σ q % 256) 1
        let b := (qAvalanche σ q / 256) % 256
        have ha_lt_256 : a < 256 := by
          have h_lor_lt256 : ∀ x < 256, Nat.lor x 1 < 256 := by decide
          apply h_lor_lt256
          exact Nat.mod_lt _ (by decide : 0 < 256)
        have hb_lt_256 : b < 256 := Nat.mod_lt _ (by decide : 0 < 256)
        have h_eq256 : (a * v + b) % 256 = v := by
          simpa [a, b] using h_av_b_mod256
        let r := (a * v) % 256
        have hr_lt_256 : r < 256 := Nat.mod_lt (a * v) (by decide : 0 < 256)
        have h_rb_mod256 : (r + b) % 256 = v := by
          calc
            (r + b) % 256 = ((a * v) % 256 + b) % 256 := rfl
            _ = (a * v + b) % 256 := by omega
            _ = v := h_eq256
        have h_rb_lt_512 : r + b < 512 := by omega
        by_cases h_rb_lt_256 : r + b < 256
        · have h_rb_eq_v : r + b = v := by
            have h_mod : (r + b) % 256 = v := h_rb_mod256
            omega
          have h_b_expr : b = (256 + v - r) % 256 := by
            have : r ≤ v := by omega
            omega
          calc
            (qAvalanche σ q / 256) % 256 = b := rfl
            _ = (256 + v - r) % 256 := h_b_expr
            _ = (256 + v - ((Nat.lor (qAvalanche σ q % 256) 1 * v) % 256)) % 256 := rfl
        · have h_rb_eq_v_plus_256 : r + b = v + 256 := by
            have h_mod : (r + b) % 256 = v := h_rb_mod256
            omega
          have h_b_expr : b = (256 + v - r) % 256 := by
            have : r > v := by omega
            omega
          calc
            (qAvalanche σ q / 256) % 256 = b := rfl
            _ = (256 + v - r) % 256 := h_b_expr
            _ = (256 + v - ((Nat.lor (qAvalanche σ q % 256) 1 * v) % 256)) % 256 := rfl

      let mix := λ σ => qAvalanche σ q
      let a := λ σ => Nat.lor (mix σ % 256) 1
      let lo := λ σ => mix σ % 256
      let lo_bit := λ σ => if lo σ = a σ then 1 else 0
      let hival := λ σ => mix σ / 65536
      let idx := λ σ => (((a σ - 1) / 2) * 2 + lo_bit σ) * 2 ^ 48 + hival σ

      have hmix_lt (σ : Nat) : mix σ < 2 ^ 64 := by
        dsimp [mix]; apply qAvalanche_lt_two_pow

      have ha_range (σ : Nat) : a σ < 256 := by
        dsimp [a]
        have h_mod_lt : mix σ % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
        have h_lor_lt : ∀ x < 256, Nat.lor x 1 < 256 := by decide
        exact h_lor_lt _ h_mod_lt

      have ha_odd (σ : Nat) : a σ % 2 = 1 := by
        dsimp [a, mix]
        have h_all_lt256 : ∀ x < 256, (Nat.lor x 1) % 2 = 1 := by decide
        exact h_all_lt256 (qAvalanche σ q % 256) (Nat.mod_lt _ (by decide : 0 < 256))

      have h_hival_lt (σ : Nat) : hival σ < 2 ^ 48 := by
        dsimp [hival, mix]
        have h_mix_lt : qAvalanche σ q < 2 ^ 64 := hmix_lt σ
        have h_div_lt : qAvalanche σ q / 65536 < 2 ^ 64 / 65536 :=
          Nat.div_lt_of_lt_mul h_mix_lt
        calc
          qAvalanche σ q / 65536 < 2 ^ 64 / 65536 := h_div_lt
          _ = 2 ^ 48 := by native_decide

      have h_idx_lt_2pow56 (σ : Nat) : idx σ < 2 ^ 56 := by
        unfold idx
        have ha_val_le : ((a σ - 1) / 2) * 2 + lo_bit σ ≤ 255 := by
          have ha_le : a σ ≤ 255 := by
            have h := ha_range σ
            omega
          have h_lo_bit_le : lo_bit σ ≤ 1 := by
            unfold lo_bit; split <;> omega
          omega
        have h_hival_lt_48 : hival σ < 2 ^ 48 := h_hival_lt σ
        calc
          (((a σ - 1) / 2) * 2 + lo_bit σ) * 2 ^ 48 + hival σ
              ≤ 255 * 2 ^ 48 + (2 ^ 48 - 1) := by
                have hval : ((a σ - 1) / 2) * 2 + lo_bit σ ≤ 255 := ha_val_le
                have hhival_le : hival σ ≤ 2 ^ 48 - 1 := by omega
                omega
          _ = 256 * 2 ^ 48 - 1 := by omega
          _ = 2 ^ 56 - 1 := by native_decide
          _ < 2 ^ 56 := by omega

      have h_idx_inj : ∀ i j, i < 2 ^ 56 + 1 → j < 2 ^ 56 + 1 → idx i = idx j → i = j := by
        intro i j hi_lt hj_lt hidx_eq
        unfold idx at hidx_eq

        have h_hival_i_lt : hival i < 2 ^ 48 := h_hival_lt i
        have h_hival_j_lt : hival j < 2 ^ 48 := h_hival_lt j

        have h_mod_eq : hival i = hival j := by
          calc
            hival i = hival i % 2 ^ 48 := by rw [Nat.mod_eq_of_lt h_hival_i_lt]
            _ = (0 + hival i) % 2 ^ 48 := by simp
            _ = ((((a i - 1) / 2) * 2 + lo_bit i) * 2 ^ 48 + hival i) % 2 ^ 48 := by simp [Nat.add_mod]
            _ = ((((a j - 1) / 2) * 2 + lo_bit j) * 2 ^ 48 + hival j) % 2 ^ 48 := by rw [hidx_eq]
            _ = hival j % 2 ^ 48 := by simp [Nat.add_mod]
            _ = hival j := by rw [Nat.mod_eq_of_lt h_hival_j_lt]

        have h_val_eq : ((a i - 1) / 2) * 2 + lo_bit i = ((a j - 1) / 2) * 2 + lo_bit j := by
          omega

        have h_lor_odd : ∀ n < 256, n % 2 = 1 → Nat.lor n 1 = n := by decide
        have h_lor_even : ∀ n < 256, n % 2 = 0 → Nat.lor n 1 = n + 1 := by decide

        have h_lo_eq_coeff (σ : Nat) : ((a σ - 1) / 2) * 2 + lo_bit σ = lo σ := by
          have h_lt : lo σ < 256 := by
            unfold lo
            exact Nat.mod_lt _ (by decide : 0 < 256)
          by_cases h_odd : lo σ % 2 = 1
          · have h_lor : Nat.lor (lo σ) 1 = lo σ := h_lor_odd (lo σ) h_lt h_odd
            have ha_eq : a σ = lo σ := by
              unfold a
              calc
                Nat.lor (mix σ % 256) 1 = Nat.lor (lo σ) 1 := rfl
                _ = lo σ := h_lor
            have h_lo_bit_eq : lo_bit σ = 1 := by
              unfold lo_bit
              simp [ha_eq.symm]
            calc
              ((a σ - 1) / 2) * 2 + lo_bit σ = ((lo σ - 1) / 2) * 2 + 1 := by rw [ha_eq, h_lo_bit_eq]
              _ = lo σ := by
                have h_mul : ((lo σ - 1) / 2) * 2 = lo σ - 1 := by
                  have h_div_add := Nat.div_add_mod (lo σ - 1) 2
                  omega
                omega
          · have h_even : lo σ % 2 = 0 := by omega
            have h_lor : Nat.lor (lo σ) 1 = lo σ + 1 := h_lor_even (lo σ) h_lt h_even
            have ha_eq : a σ = lo σ + 1 := by
              unfold a
              calc
                Nat.lor (mix σ % 256) 1 = Nat.lor (lo σ) 1 := rfl
                _ = lo σ + 1 := h_lor
            have h_lo_bit_eq : lo_bit σ = 0 := by
              unfold lo_bit
              have ha_ne : lo σ ≠ a σ := by
                intro h_eq
                have : lo σ = lo σ + 1 := by
                  calc
                    lo σ = a σ := h_eq
                    _ = lo σ + 1 := ha_eq
                omega
              simp [ha_ne]
            calc
              ((a σ - 1) / 2) * 2 + lo_bit σ = ((lo σ + 1 - 1) / 2) * 2 + 0 := by rw [ha_eq, h_lo_bit_eq]
              _ = (lo σ / 2) * 2 := by omega
              _ = lo σ := by
                have h_mul : (lo σ / 2) * 2 = lo σ := by
                  have h_div_add := Nat.div_add_mod (lo σ) 2
                  omega
                rw [h_mul]

        have h_lo_eq : lo i = lo j := by
          calc
            lo i = ((a i - 1) / 2) * 2 + lo_bit i := (h_lo_eq_coeff i).symm
            _ = ((a j - 1) / 2) * 2 + lo_bit j := h_val_eq
            _ = lo j := h_lo_eq_coeff j

        have hmix_low_eq : mix i % 256 = mix j % 256 := by
          unfold lo at h_lo_eq
          exact h_lo_eq

        have hmix_mid_eq : (mix i / 256) % 256 = (mix j / 256) % 256 := by
          calc
            (mix i / 256) % 256 = (256 + v - ((Nat.lor (mix i % 256) 1 * v) % 256)) % 256 := h_b_det i
            _ = (256 + v - ((Nat.lor (mix j % 256) 1 * v) % 256)) % 256 := by simp [hmix_low_eq]
            _ = (mix j / 256) % 256 := by rw [h_b_det j]

        have hmix_high_eq : mix i / 65536 = mix j / 65536 := by
          unfold hival at h_mod_eq
          exact h_mod_eq

        have h_low16_eq : mix i % 65536 = mix j % 65536 := by
          have h_mod256_dvd (x : Nat) : (x % 65536) % 256 = x % 256 := by
            calc
              (x % 65536) % 256 = (x % (256 * 256 : Nat)) % 256 := by
                have : 65536 = 256 * 256 := by native_decide
                rw [this]
              _ = x % 256 := by simp
          have h_div256_dvd (x : Nat) : (x % 65536) / 256 = (x / 256) % 256 := by
            have h_lt : x % 65536 < 65536 := Nat.mod_lt _ (by decide : 0 < 65536)
            omega
          have h_low16_expr (x : Nat) : x % 65536 = (x % 256) + 256 * ((x / 256) % 256) := by
            calc
              x % 65536 = ((x % 65536) % 256) + 256 * ((x % 65536) / 256) := by
                have h := Nat.div_add_mod (x % 65536) 256
                omega
              _ = (x % 256) + 256 * ((x / 256) % 256) := by rw [h_mod256_dvd, h_div256_dvd]
          calc
            mix i % 65536 = (mix i % 256) + 256 * ((mix i / 256) % 256) := h_low16_expr _
            _ = (mix j % 256) + 256 * ((mix j / 256) % 256) := by rw [hmix_low_eq, hmix_mid_eq]
            _ = mix j % 65536 := (h_low16_expr _).symm

        have hmix_eq : mix i = mix j := by
          calc
            mix i = (mix i / 65536) * 65536 + (mix i % 65536) := by omega
            _ = (mix j / 65536) * 65536 + (mix j % 65536) := by rw [hmix_high_eq, h_low16_eq]
            _ = mix j := by omega

        have hi_lt_64 : i < 2 ^ 64 := by
          have : 2 ^ 56 + 1 < 2 ^ 64 := by native_decide
          omega
        have hj_lt_64 : j < 2 ^ 64 := by
          have : 2 ^ 56 + 1 < 2 ^ 64 := by native_decide
          omega
        exact h_inj i j hi_lt_64 hj_lt_64 hmix_eq

      have h_range : ∀ i, i < 2 ^ 56 + 1 → idx i < 2 ^ 56 :=
        λ i hi => h_idx_lt_2pow56 i

      exact no_inj_gt_range idx (2 ^ 56) h_range h_idx_inj
    exact h_contra


/-- K3: Bridge output varies with state.

    For any `c0, anchor, c1_t, c2` and any QAvalancheConfig with odd multiplier
    and xor_shift ≥ 1, there exist `(σ₁,σ₂,DDM₁,DDM₂)` giving different bridge outputs. -/
theorem K3_bridge_varies_with_state (c0 anchor c1_t c2 : Nat) (q : QAvalancheConfig) (invMult : Nat)
    (h_inv : (q.mult * invMult) % 2 ^ 64 = 1) (h_shift : 1 ≤ q.xor_shift) :
    ∃ (σ₁ σ₂ DDM₁ DDM₂ : Nat), bridge_i41 c0 anchor c1_t c2 σ₁ DDM₁ q q ≠
                             bridge_i41 c0 anchor c1_t c2 σ₂ DDM₂ q q := by
  have h0 : qAvalanche 0 q = 0 := qAvalanche_zero q
  have hperm0 (x : Nat) : permute x 0 q = x % 256 := by
    unfold permute; simp [h0, P_mod]

  have h_perm_mod_val (val state : Nat) (q : QAvalancheConfig) : permute (val % 256) state q = permute val state q := by
    calc
      permute (val % 256) state q = ((Nat.lor (qAvalanche state q % 256) 1 * (val % 256) + (qAvalanche state q / 256) % 256) % 256) := by rw [permute_eq_mod_form]
      _ = ((Nat.lor (qAvalanche state q % 256) 1 * val + (qAvalanche state q / 256) % 256) % 256) := by
        simp [Nat.mul_mod, Nat.add_mod]
      _ = permute val state q := by rw [permute_eq_mod_form]

  let v := c1_t % 256
  have hv_lt : v < 256 := Nat.mod_lt _ (by decide : 0 < 256)

  by_cases h_diff : ∃ σ₂, permute c1_t σ₂ q ≠ c1_t % 256
  · rcases h_diff with ⟨σ₂, hσ₂⟩
    refine ⟨σ₂, 0, 0, 0, ?_⟩
    unfold bridge_i41
    have h_perm0 : permute c1_t 0 q = c1_t % 256 := hperm0 c1_t
    have h_cancel0 : permute c2 0 q ^^^ permute c2 0 q = 0 := Nat.xor_self _
    calc
      c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q ^^^ permute c2 0 q ^^^ permute c2 0 q
          = c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q := by
            simp [h_cancel0, Nat.xor_assoc]
      _ ≠ c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := by
        intro h_eq
        apply hσ₂
        calc
          permute c1_t σ₂ q = c0 ^^^ (c0 ^^^ permute c1_t σ₂ q ^^^ permute anchor 0 q) ^^^ permute anchor 0 q :=
            (xor_quad_cancel c0 (permute c1_t σ₂ q) (permute anchor 0 q)).symm
          _ = c0 ^^^ (c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q) ^^^ permute anchor 0 q := by rw [h_eq]
          _ = c1_t % 256 := xor_quad_cancel c0 (c1_t % 256) (permute anchor 0 q)
      _ = c0 ^^^ permute c1_t 0 q ^^^ permute anchor 0 q ^^^ permute c2 0 q ^^^ permute c2 0 q := by
        simp [h_perm0, h_cancel0, Nat.xor_assoc]
  · -- h_diff: ∀ σ₂, permute c1_t σ₂ q = c1_t % 256
    by_cases h_diff' : ∃ DDM₂, permute c2 DDM₂ q ≠ c2 % 256
    · rcases h_diff' with ⟨DDM₂, hDDM₂⟩
      refine ⟨0, 0, 0, DDM₂, ?_⟩
      unfold bridge_i41
      have h_perm0_c1 : permute c1_t 0 q = c1_t % 256 := hperm0 c1_t
      have h_perm0_c2 : permute c2 0 q = c2 % 256 := hperm0 c2
      have h_nonzero : permute c2 DDM₂ q ^^^ permute c2 0 q ≠ 0 := by
        intro hz
        apply hDDM₂
        calc
          permute c2 DDM₂ q = permute c2 DDM₂ q ^^^ 0 := by simp
          _ = (permute c2 DDM₂ q ^^^ permute c2 0 q) ^^^ permute c2 0 q := by
            simp [Nat.xor_assoc]
          _ = 0 ^^^ permute c2 0 q := by rw [hz]
          _ = permute c2 0 q := by simp
          _ = c2 % 256 := h_perm0_c2
      calc
        c0 ^^^ permute c1_t 0 q ^^^ permute anchor 0 q ^^^ permute c2 0 q ^^^ permute c2 0 q
            = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ permute c2 0 q ^^^ permute c2 0 q := by rw [h_perm0_c1]
        _ = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ (permute c2 0 q ^^^ permute c2 0 q) := by simp [Nat.xor_assoc]
        _ = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ 0 := by rw [Nat.xor_self]
        _ = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := by simp
        _ ≠ c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q ^^^ permute c2 DDM₂ q ^^^ permute c2 0 q := by
          intro h_eq
          apply h_nonzero
          have htemp : permute c2 DDM₂ q ^^^ permute c2 0 q = 0 :=
            (xor_left_cancel (c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q) 0
              (permute c2 DDM₂ q ^^^ permute c2 0 q) (by
                calc
                  (c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q) ^^^ 0
                      = c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q := by simp
                  _ = (c0 ^^^ (c1_t % 256) ^^^ permute anchor 0 q) ^^^ (permute c2 DDM₂ q ^^^ permute c2 0 q) := by
                    simpa [Nat.xor_assoc] using h_eq)).symm
          exact htemp
        _ = c0 ^^^ permute c1_t 0 q ^^^ permute anchor 0 q ^^^ permute c2 DDM₂ q ^^^ permute c2 0 q := by
          rw [h_perm0_c1]
    · -- h_diff': ∀ DDM₂, permute c2 DDM₂ q = c2 % 256
      exfalso
      have h_exists : ∃ σ, permute (c1_t % 256) σ q ≠ c1_t % 256 :=
        exists_sigma_permute_diff (c1_t % 256) (Nat.mod_lt _ (by decide : 0 < 256)) q invMult h_inv h_shift
      rcases h_exists with ⟨σ, hσ⟩
      have h_all_σ : permute c1_t σ q = c1_t % 256 := by
        by_cases h_eq : permute c1_t σ q = c1_t % 256
        · exact h_eq
        · exfalso
          exact h_diff ⟨σ, h_eq⟩
      apply hσ
      calc
        permute (c1_t % 256) σ q = permute c1_t σ q := h_perm_mod_val c1_t σ q
        _ = c1_t % 256 := h_all_σ
