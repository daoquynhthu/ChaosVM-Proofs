import ChaosvmProofs.Definitions.Helpers
import Init.Omega

/-! # P(x,s) bijective affine map (Rust: `sem_share.rs:56`, `reg_map.rs`). -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

/-- For any odd a < 256, exists aInv < 256 with (a * aInv) % 256 = 1. -/
theorem exists_mod_inv (a : Nat) (ha_lt : a < 256) (ha_odd : a % 2 = 1) : ∃ aInv, aInv < 256 ∧ (a * aInv) % 256 = 1 := by
  have h : ∀ x, x < 256 → x % 2 = 1 → ∃ y, y < 256 ∧ (x * y) % 256 = 1 := by
    decide
  exact h a ha_lt ha_odd

/-- For any odd a : ℕ, exists aInv with (a * aInv) % 256 = 1. -/
theorem exists_mod_inv_any (a : Nat) (ha_odd : a % 2 = 1) : ∃ aInv, (a * aInv) % 256 = 1 := by
  have ha_mod : (a % 256) % 2 = 1 := by
    have h2_256 : 2 ∣ 256 := by decide
    have h := Nat.mod_mod_of_dvd (c := 2) (b := 256) a h2_256
    calc
      (a % 256) % 2 = a % 2 := h
      _ = 1 := ha_odd
  have ha_mod_lt : a % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  rcases exists_mod_inv (a % 256) ha_mod_lt ha_mod with ⟨aInv, haInv_lt, h⟩
  refine ⟨aInv, ?_⟩
  calc
    (a * aInv) % 256 = ((a % 256) * aInv) % 256 := by
      simp [Nat.mul_mod]
    _ = 1 := h

/-- P(x, a, b) = (a·x + b) % 256. -/
def P_mod (x a b : Nat) : Nat := (a * x + b) % 256

/-- If (X+B)%256 = (Y+B)%256 with X,Y,B < 256, then X = Y. -/
theorem add_mod_inj (X Y B : Nat) (hX : X < 256) (hY : Y < 256) (_hB : B < 256)
    (h_eq : (X + B) % 256 = (Y + B) % 256) : X = Y := by
  omega

/-- P_mod is injective on {x | x < 256} when a is odd. -/
theorem P_mod_inj_mod (a b : Nat) (ha_odd : a % 2 = 1) (x y : Nat) (hx : x < 256) (hy : y < 256)
    (h_eq : P_mod x a b = P_mod y a b) : x = y := by
  rcases exists_mod_inv_any a ha_odd with ⟨aInv, h_inv⟩
  have h_inv' : (aInv * a) % 256 = 1 := by
    simpa [Nat.mul_comm] using h_inv
  unfold P_mod at h_eq
  have hax_lt : (a * x) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  have hay_lt : (a * y) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  have hb_mod_lt : b % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  -- Step 1: (a*x)%256 = (a*y)%256 by add_mod_inj
  have h_mod_eq : (a * x) % 256 = (a * y) % 256 := by
    apply add_mod_inj ((a * x) % 256) ((a * y) % 256) (b % 256)
      hax_lt hay_lt hb_mod_lt
    calc
      (((a * x) % 256) + (b % 256)) % 256 = (a * x + b) % 256 := by simp [Nat.add_mod]
      _ = (a * y + b) % 256 := h_eq
      _ = (((a * y) % 256) + (b % 256)) % 256 := by simp [Nat.add_mod]
  -- Step 2: Multiply by aInv: aInv·(a·x) ≡ aInv·(a·y) (mod 256)
  have hx_mod_eq_hy_mod : x % 256 = y % 256 := by
    calc
      x % 256 = (1 * x) % 256 := by simp
      _ = ((aInv * a) % 256 * x) % 256 := by
        rw [h_inv']
      _ = ((aInv * a) * x) % 256 := by simp [Nat.mul_mod]
      _ = (aInv * (a * x)) % 256 := by
        rw [Nat.mul_assoc]
      _ = (aInv * ((a * x) % 256)) % 256 := by simp [Nat.mul_mod]
      _ = (aInv * ((a * y) % 256)) % 256 := by rw [h_mod_eq]
      _ = (aInv * (a * y)) % 256 := by simp [Nat.mul_mod]
      _ = ((aInv * a) * y) % 256 := by
        rw [← Nat.mul_assoc]
      _ = ((aInv * a) % 256 * y) % 256 := by simp [Nat.mul_mod]
      _ = (1 * y) % 256 := by
        rw [h_inv']
      _ = y % 256 := by simp
  -- Step 3: x<256 ∧ y<256 → x%256 = x, y%256 = y
  have hx_mod : x % 256 = x := Nat.mod_eq_of_lt hx
  have hy_mod : y % 256 = y := Nat.mod_eq_of_lt hy
  rw [hx_mod, hy_mod] at hx_mod_eq_hy_mod
  exact hx_mod_eq_hy_mod

/-- P_mod is injective on Fin 256 for odd a. -/
theorem P_mod_injective (a b : Nat) (ha_odd : a % 2 = 1) : Function.Injective (λ (x : Fin 256) => P_mod x.val a b) := by
  intro x y h
  apply Fin.ext
  exact P_mod_inj_mod a b ha_odd x.val y.val x.2 y.2 h

/-- P_mod is surjective on Fin 256 for odd a.

    Constructive inverse: x = (aInv · ((y + 256 - b%256) % 256)) % 256,
    where aInv satisfies (a·aInv) % 256 = 1. -/
theorem P_mod_surjective (a b : Nat) (ha_odd : a % 2 = 1) : ∀ (y : Fin 256), ∃ (x : Fin 256), P_mod x.val a b = y.val := by
  rcases exists_mod_inv_any a ha_odd with ⟨aInv, h_inv⟩
  intro y
  let b_mod := b % 256
  have hb_mod_lt : b_mod < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  -- z = (y.val + 256 - b_mod) % 256  is (y.val - b_mod) modulo 256, always non-negative
  let z := (y.val + 256 - b_mod) % 256
  have hz_lt : z < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  let x_val := (aInv * z) % 256
  have hx_val_lt : x_val < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  let x : Fin 256 := ⟨x_val, hx_val_lt⟩
  refine ⟨x, ?_⟩
  calc
    P_mod x.val a b = (a * ((aInv * z) % 256) + b) % 256 := rfl
    _ = ((a * ((aInv * z) % 256)) % 256 + b % 256) % 256 := by
      simp [Nat.add_mod]
    _ = ((a * (aInv * z)) % 256 + b % 256) % 256 := by
      have h_mul : (a * ((aInv * z) % 256)) % 256 = (a * (aInv * z)) % 256 := by
        calc
          (a * ((aInv * z) % 256)) % 256 = ((a % 256) * (((aInv * z) % 256) % 256)) % 256 := by
            simp [Nat.mul_mod]
          _ = ((a % 256) * ((aInv * z) % 256)) % 256 := by simp
          _ = (a * (aInv * z)) % 256 := by simp [Nat.mul_mod]
      rw [h_mul]
    _ = (a * (aInv * z) + b) % 256 := by simp [Nat.add_mod]
    _ = (((a * aInv) * z) + b) % 256 := by
      rw [← Nat.mul_assoc]
    _ = (((a * aInv) % 256 * z) + b) % 256 := by
      calc
        (((a * aInv) * z) + b) % 256 = ((((a * aInv) * z) % 256) + (b % 256)) % 256 := by
          simp [Nat.add_mod]
        _ = ((((a * aInv) % 256) * (z % 256) % 256) + (b % 256)) % 256 := by
          simp [Nat.mul_mod]
        _ = ((((a * aInv) % 256) * z % 256) + (b % 256)) % 256 := by
          have hz_mod : z % 256 = z := Nat.mod_eq_of_lt hz_lt
          simp [hz_mod]
        _ = (((a * aInv) % 256 * z) + b) % 256 := by
          simp [Nat.add_mod]
    _ = ((1 * z) + b) % 256 := by rw [h_inv]
    _ = (z + b_mod) % 256 := by
      simp [show b_mod = b % 256 from rfl, Nat.add_mod]
    _ = ((y.val + 256 - b_mod) % 256 + b_mod) % 256 := rfl
    _ = y.val := by
      omega

/-- P_mod is bijective on Fin 256 for odd a (injective ∧ surjective). -/
theorem P_mod_bijective (a b : Nat) (ha_odd : a % 2 = 1) :
    Function.Injective (λ (x : Fin 256) => P_mod x.val a b) ∧
    (∀ (y : Fin 256), ∃ (x : Fin 256), P_mod x.val a b = y.val) := by
  constructor
  · exact P_mod_injective a b ha_odd
  · exact P_mod_surjective a b ha_odd

/-- P_of_state(x, state) approximates Rust `permute(val, state, q)`.

    Rust derives (a,b) via `q_avalanche(state, q)`. Lean uses `state` directly
    as the entropy source (bypassing the abstract QAvalanche). Since `q_avalanche`
    is modeled as identity in the formal proof, both versions coincide algebraically.

    The key property (a is odd → bijective) holds in both versions:
      Rust:  a = (q_avalanche(state,q) & 0xFF) | 1  → odd
      Lean:  a = (state & 0xFF) | 1                  → odd
    -/
def P_of_state (x state : Nat) : Nat :=
  let a := Nat.lor (state % 256) 1
  let b := (state / 256) % 256
  P_mod x a b

/-- P_of_state is bijective on Fin 256 (a is always odd). -/
theorem P_of_state_bijective (state : Nat) :
    Function.Injective (λ (x : Fin 256) => P_of_state x.val state) ∧
    (∀ (y : Fin 256), ∃ (x : Fin 256), P_of_state x.val state = y.val) := by
  unfold P_of_state
  let a := Nat.lor (state % 256) 1
  have ha_odd : a % 2 = 1 := by
    have h_all : ∀ x < 256, (Nat.lor x 1) % 2 = 1 := by
      decide
    exact h_all (state % 256) (Nat.mod_lt _ (by decide : 0 < 256))
  exact P_mod_bijective a ((state / 256) % 256) ha_odd

/-- Affine register map (Rust: `reg_map.rs`), identical to P_mod. -/
def affine_map (r a b : Nat) : Nat := P_mod r a b

/-- affine_map is bijective on Fin 256 for odd a. -/
theorem affine_map_bijective (a b : Nat) (ha_odd : a % 2 = 1) :
    Function.Injective (λ (r : Fin 256) => affine_map r.val a b) ∧
    (∀ (y : Fin 256), ∃ (r : Fin 256), affine_map r.val a b = y.val) :=
  P_mod_bijective a b ha_odd

/-- IsOdd predicate. -/
def IsOdd (a : Nat) : Prop := a % 2 = 1
