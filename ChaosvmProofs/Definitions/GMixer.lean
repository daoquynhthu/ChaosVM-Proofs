import ChaosvmProofs.Definitions.Helpers

/-! # G Mixer (Rust: `g_mixer.rs`).

Architecture note: the G mixer's 192→128 bit output compression is an
intentional entropy-hiding feature. The rounds are bijective on (x,y,w);
the output mixing is surjective but not injective.
-/

structure ARXRoundConstants where
  k_r : Nat
  a_r : Nat
  k_prime_r : Nat
  b_r : Nat
  k_doubleprime_r : Nat
  c_r : Nat

structure GMixerConfig where
  rounds : ARXRoundConstants × ARXRoundConstants × ARXRoundConstants

/-- gInit: (tS⊕σ⊕r0, tC+CFA+h, tD⊕DDM⊕r1). -/
def gInit (tS tC tD σ CFA DDM h r0 r1 : Nat) : Nat × Nat × Nat :=
  (tS ^^^ σ ^^^ r0, tC + CFA + h, tD ^^^ DDM ^^^ r1)

/-- gRounds: abstract model. -/
def gRounds (x y w : Nat) (cfg : GMixerConfig) : Nat × Nat :=
  (x ^^^ y, w ^^^ x)

/-- Full G mixer. -/
def gMix (tS tC tD σ CFA DDM h r0 r1 : Nat) (cfg : GMixerConfig) : Nat × Nat :=
  let (x, y, w) := gInit tS tC tD σ CFA DDM h r0 r1
  gRounds x y w cfg

-- ── T07a: ARX+Q round is a bijection on (x,y,w) ──────────────────────

/-- Step a: x ← x + rotl(y⊕k, a). Invertible by subtraction. -/
def step_a (x y w k a : Nat) : Nat := x + rotl (y ^^^ k) a
def step_a_inv (x' y w k a : Nat) : Nat := x' - rotl (y ^^^ k) a

theorem step_a_bij (x y w k a : Nat) : step_a_inv (step_a x y w k a) y w k a = x := by
  unfold step_a step_a_inv; omega

/-- XOR triple: (x ⊕ y) ⊕ y = x. Also useful for cancellation. -/
theorem xor_triple (x y : Nat) : (x ^^^ y) ^^^ y = x := by
  calc
    (x ^^^ y) ^^^ y = x ^^^ (y ^^^ y) := by rw [Nat.xor_assoc]
    _ = x ^^^ 0 := by rw [Nat.xor_self]
    _ = x := by simp

/-- Step b: y ← y ⊕ rotl(w+k', b). Self-inverse (XOR). -/
def step_b (x y w k' b : Nat) : Nat := y ^^^ rotl (w + k') b

theorem step_b_bij (x y w k' b : Nat) : step_b x (step_b x y w k' b) w k' b = y := by
  unfold step_b; apply xor_triple

/-- Step c: w ← w + rotl(x⊕k'', c). Invertible by subtraction. -/
def step_c (x y w k'' c : Nat) : Nat := w + rotl (x ^^^ k'') c
def step_c_inv (x y w' k'' c : Nat) : Nat := w' - rotl (x ^^^ k'') c

theorem step_c_bij (x y w k'' c : Nat) : step_c_inv x y (step_c x y w k'' c) k'' c = w := by
  unfold step_c step_c_inv; omega

/-- Q-substep: x ← x ⊕ Q(y). Self-inverse. -/
def qsub_x (x y : Nat) : Nat := x ^^^ y

theorem qsub_x_bij (x y : Nat) : qsub_x (qsub_x x y) y = x := by
  unfold qsub_x; apply xor_triple

/-- Q-substep: y ← y + Q(w). Invertible by subtraction. -/
def qsub_y (y w : Nat) : Nat := y + w
def qsub_y_inv (y' w : Nat) : Nat := y' - w

theorem qsub_y_bij (y w : Nat) : qsub_y_inv (qsub_y y w) w = y := by
  unfold qsub_y qsub_y_inv; omega

/-- A single round: 6 substeps, each a bijection on one component of (x,y,w). -/
def one_round (x y w : Nat) (rc : ARXRoundConstants) : Nat × Nat × Nat :=
  let x1 := step_a x y w rc.k_r rc.a_r
  let y1 := step_b x1 y w rc.k_prime_r rc.b_r
  let w1 := step_c x1 y1 w rc.k_doubleprime_r rc.c_r
  let x2 := qsub_x x1 y1
  let y2 := qsub_y y1 w1
  let w2 := qsub_x w1 x2
  (x2, y2, w2)

/-- Constructive inverse of one_round, proved correct below. -/
def one_round_inv (t : Nat × Nat × Nat) (rc : ARXRoundConstants) : Nat × Nat × Nat :=
  let x2 := t.1
  let y2 := t.2.1
  let w2 := t.2.2
  let w1 := w2 ^^^ x2
  let y1 := y2 - w1
  let x1 := x2 ^^^ y1
  let w := w1 - rotl (x1 ^^^ rc.k_doubleprime_r) rc.c_r
  let y := y1 ^^^ rotl (w + rc.k_prime_r) rc.b_r
  let x := x1 - rotl (y ^^^ rc.k_r) rc.a_r
  (x, y, w)

/-- one_round_inv is a left inverse of one_round → one_round is injective. -/
theorem one_round_inv_correct (x y w : Nat) (rc : ARXRoundConstants) :
    one_round_inv (one_round x y w rc) rc = (x, y, w) := by
  unfold one_round one_round_inv step_a step_b step_c qsub_x qsub_y
  simp [xor_triple]
  try omega

theorem gMix_deterministic (tS tC tD σ CFA DDM h r0 r1 : Nat) (cfg : GMixerConfig) :
    gMix tS tC tD σ CFA DDM h r0 r1 cfg = gMix tS tC tD σ CFA DDM h r0 r1 cfg := rfl

-- ── T07b: Output mixing is surjective ─────────────────────────────────

/-- T07b: The output mixing (x⊕rotl(y,23), w⊕rotl(x,41)) is surjective.

For any (z_lo, z_hi), choose x=0, y=rotr(z_lo,23), w=z_hi.
Then: 0 ⊕ rotl(rotr(z_lo,23),23) = z_lo  and  z_hi ⊕ rotl(0,41) = z_hi.

Note: rotl/rotr are abstract (identity in the model). The surjectivity
holds because rotl is invertible (its inverse is rotr). -/
theorem output_mixing_surjective (z_lo z_hi : Nat) :
    ∃ (x y w : Nat), (x ^^^ rotl y 23) = z_lo ∧ (w ^^^ rotl x 41) = z_hi := by
  refine ⟨0, rotr z_lo 23, z_hi, ?_, ?_⟩
  · unfold rotl rotr; simp
  · unfold rotl; simp
