import ChaosvmProofs.Definitions.Helpers
import ChaosvmProofs.Definitions.QAvalanche

/-! # G Mixer (Rust: `g_mixer.rs`).

Architecture note: the G mixer's 192→128 bit output compression is an
intentional entropy-hiding feature. The rounds are bijective on (x,y,w);
the output mixing is surjective but not injective.

The Q substeps use the concrete `qAvalanche` function (multiply-mod-2^64,
XOR-shift, rotate-left), matching the Rust implementation faithfully.
-/

structure ARXRoundConstants where
  k_r : Nat
  a_r : Nat
  k_prime_r : Nat
  b_r : Nat
  k_doubleprime_r : Nat
  c_r : Nat

/-- Full G mixer config matching Rust `GMixerConfig`.
    Uses QAvalancheConfig (identical to QAvalancheRound in Rust). -/
structure GMixerConfig where
  rounds : ARXRoundConstants × ARXRoundConstants × ARXRoundConstants
  q       : QAvalancheConfig × QAvalancheConfig × QAvalancheConfig
  q_prime : QAvalancheConfig × QAvalancheConfig × QAvalancheConfig
  q_doubleprime : QAvalancheConfig × QAvalancheConfig × QAvalancheConfig

/-- gInit: (tS⊕σ⊕r0, tC+CFA+h, tD⊕DDM⊕r1). -/
def gInit (tS tC tD σ CFA DDM h r0 r1 : Nat) : Nat × Nat × Nat :=
  (tS ^^^ σ ^^^ r0, tC + CFA + h, tD ^^^ DDM ^^^ r1)

-- ── T07a: ARX+Q round is a bijection on (x,y,w) ──────────────────────

/-- Sub-step a: x ← x + rotl(y⊕k, a). Invertible by subtraction. -/
def step_a (x y _w k a : Nat) : Nat := x + rotl (y ^^^ k) a
def step_a_inv (x' y _w k a : Nat) : Nat := x' - rotl (y ^^^ k) a

theorem step_a_bij (x y w k a : Nat) : step_a_inv (step_a x y w k a) y w k a = x := by
  unfold step_a step_a_inv; omega

/-- XOR triple. -/
theorem xor_triple (x y : Nat) : (x ^^^ y) ^^^ y = x := by
  calc
    (x ^^^ y) ^^^ y = x ^^^ (y ^^^ y) := by rw [Nat.xor_assoc]
    _ = x ^^^ 0 := by rw [Nat.xor_self]
    _ = x := by simp

/-- Sub-step b: y ← y ⊕ rotl(w+k', b). Self-inverse. -/
def step_b (_x y w k' b : Nat) : Nat := y ^^^ rotl (w + k') b
theorem step_b_bij (x y w k' b : Nat) : step_b x (step_b x y w k' b) w k' b = y := by
  unfold step_b; apply xor_triple

/-- Sub-step c: w ← w + rotl(x⊕k'', c). Invertible. -/
def step_c (x _y w k'' c : Nat) : Nat := w + rotl (x ^^^ k'') c
def step_c_inv (x _y w' k'' c : Nat) : Nat := w' - rotl (x ^^^ k'') c
theorem step_c_bij (x y w k'' c : Nat) : step_c_inv x y (step_c x y w k'' c) k'' c = w := by
  unfold step_c step_c_inv; omega

/-- Q-substep: x ← x ⊕ qAvalanche(y, cfg). Self-inverse. -/
def qsub_x (x y : Nat) (cfg : QAvalancheConfig) : Nat := x ^^^ qAvalanche y cfg
theorem qsub_x_bij (x y : Nat) (cfg : QAvalancheConfig) : qsub_x (qsub_x x y cfg) y cfg = x := by
  unfold qsub_x; apply xor_triple

/-- Q-substep: y ← y + qAvalanche(w, cfg). Invertible. -/
def qsub_y (y w : Nat) (cfg : QAvalancheConfig) : Nat := y + qAvalanche w cfg
def qsub_y_inv (y' w : Nat) (cfg : QAvalancheConfig) : Nat := y' - qAvalanche w cfg
theorem qsub_y_bij (y w : Nat) (cfg : QAvalancheConfig) : qsub_y_inv (qsub_y y w cfg) w cfg = y := by
  unfold qsub_y qsub_y_inv; omega

/-- A single round: 6 substeps, each a bijection on one component of (x,y,w). -/
def one_round (x y w : Nat) (rc : ARXRoundConstants)
    (q q_prime q_doubleprime : QAvalancheConfig) : Nat × Nat × Nat :=
  let x1 := step_a x y w rc.k_r rc.a_r
  let y1 := step_b x1 y w rc.k_prime_r rc.b_r
  let w1 := step_c x1 y1 w rc.k_doubleprime_r rc.c_r
  let x2 := qsub_x x1 y1 q
  let y2 := qsub_y y1 w1 q_prime
  let w2 := qsub_x w1 x2 q_doubleprime
  (x2, y2, w2)

/-- Constructive inverse of one_round. -/
def one_round_inv (t : Nat × Nat × Nat) (rc : ARXRoundConstants)
    (q q_prime q_doubleprime : QAvalancheConfig) : Nat × Nat × Nat :=
  let x2 := t.1; let y2 := t.2.1; let w2 := t.2.2
  let w1 := w2 ^^^ qAvalanche x2 q_doubleprime
  let y1 := y2 - qAvalanche w1 q_prime
  let x1 := x2 ^^^ qAvalanche y1 q
  let w := w1 - rotl (x1 ^^^ rc.k_doubleprime_r) rc.c_r
  let y := y1 ^^^ rotl (w + rc.k_prime_r) rc.b_r
  let x := x1 - rotl (y ^^^ rc.k_r) rc.a_r
  (x, y, w)

theorem one_round_inv_correct (x y w : Nat) (rc : ARXRoundConstants)
    (q q_prime q_doubleprime : QAvalancheConfig) :
    one_round_inv (one_round x y w rc q q_prime q_doubleprime) rc q q_prime q_doubleprime = (x, y, w) := by
  unfold one_round one_round_inv step_a step_b step_c qsub_x qsub_y
  dsimp; simp (config := { zeta := true }) [xor_triple]

-- ── K1: three-round gRounds_internal is a bijection ─────────────────

/-- Adapt one_round to accept a triple (Nat × Nat × Nat) as input. -/
def one_round' (t : Nat × Nat × Nat) (rc : ARXRoundConstants)
    (q q_prime q_doubleprime : QAvalancheConfig) : Nat × Nat × Nat :=
  one_round t.1 t.2.1 t.2.2 rc q q_prime q_doubleprime

theorem one_round'_inv (t : Nat × Nat × Nat) (rc : ARXRoundConstants)
    (q q_prime q_doubleprime : QAvalancheConfig) :
    one_round_inv (one_round' t rc q q_prime q_doubleprime) rc q q_prime q_doubleprime = t := by
  unfold one_round'
  calc
    one_round_inv (one_round t.1 t.2.1 t.2.2 rc q q_prime q_doubleprime) rc q q_prime q_doubleprime
        = (t.1, t.2.1, t.2.2) :=
      one_round_inv_correct t.1 t.2.1 t.2.2 rc q q_prime q_doubleprime
    _ = t := rfl

/-- Internal 3-round gRounds WITHOUT output mixing (the bijective core). -/
def gRounds_internal (x y w : Nat) (cfg : GMixerConfig) : Nat × Nat × Nat :=
  let (rc1, rc2, rc3) := cfg.rounds
  let (q1, q2, q3) := cfg.q
  let (qp1, qp2, qp3) := cfg.q_prime
  let (qdp1, qdp2, qdp3) := cfg.q_doubleprime
  one_round' (one_round' (one_round' (x, y, w) rc1 q1 qp1 qdp1) rc2 q2 qp2 qdp2) rc3 q3 qp3 qdp3

/-- Constructive inverse of gRounds_internal (3 one_round inverses, reversed). -/
def gRounds_internal_inv (t : Nat × Nat × Nat) (cfg : GMixerConfig) : Nat × Nat × Nat :=
  let (rc1, rc2, rc3) := cfg.rounds
  let (q1, q2, q3) := cfg.q
  let (qp1, qp2, qp3) := cfg.q_prime
  let (qdp1, qdp2, qdp3) := cfg.q_doubleprime
  one_round_inv (one_round_inv (one_round_inv t rc3 q3 qp3 qdp3) rc2 q2 qp2 qdp2) rc1 q1 qp1 qdp1

theorem gRounds_internal_inv_correct (x y w : Nat) (cfg : GMixerConfig) :
    gRounds_internal_inv (gRounds_internal x y w cfg) cfg = (x, y, w) := by
  unfold gRounds_internal gRounds_internal_inv
  simp [one_round'_inv]

-- ── 3-round gRounds matching Rust ────────────────────────────────────

/-- Full 3-round gRounds with output mixing, matching Rust `g_rounds`. -/
def gRounds (x y w : Nat) (cfg : GMixerConfig) : Nat × Nat :=
  let (rc1, rc2, rc3) := cfg.rounds
  let (q1, q2, q3) := cfg.q
  let (qp1, qp2, qp3) := cfg.q_prime
  let (qdp1, qdp2, qdp3) := cfg.q_doubleprime
  let (x1, y1, w1) := one_round x y w rc1 q1 qp1 qdp1
  let (x2, y2, w2) := one_round x1 y1 w1 rc2 q2 qp2 qdp2
  let (x3, y3, w3) := one_round x2 y2 w2 rc3 q3 qp3 qdp3
  (x3 ^^^ rotl y3 23, w3 ^^^ rotl x3 41)

/-- Full G mixer: gInit + 3-round gRounds. -/
def gMix (tS tC tD σ CFA DDM h r0 r1 : Nat) (cfg : GMixerConfig) : Nat × Nat :=
  let (x, y, w) := gInit tS tC tD σ CFA DDM h r0 r1
  gRounds x y w cfg

theorem gMix_deterministic (tS tC tD σ CFA DDM h r0 r1 : Nat) (cfg : GMixerConfig) :
    gMix tS tC tD σ CFA DDM h r0 r1 cfg = gMix tS tC tD σ CFA DDM h r0 r1 cfg := rfl

-- ── T07b: Output mixing is surjective ─────────────────────────────────

/-- The output mixing (x⊕rotl(y,23), w⊕rotl(x,41)) is surjective.

   Choose x = z_lo, y = 0, w = z_hi ⊕ rotl(z_lo, 41).
   Then x ⊕ rotl(y,23) = z_lo  and  w ⊕ rotl(x,41) = z_hi (XOR triple). -/
theorem output_mixing_surjective (z_lo z_hi : Nat) :
    ∃ (x y w : Nat), (x ^^^ rotl y 23) = z_lo ∧ (w ^^^ rotl x 41) = z_hi := by
  refine ⟨z_lo, 0, (z_hi ^^^ rotl z_lo 41), ?_, ?_⟩
  · have h0 : rotl 0 23 = 0 := by
      unfold rotl rotl64 shl shr mask64; simp
    simp [h0]
  · apply xor_triple
