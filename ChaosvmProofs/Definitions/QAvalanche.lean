import ChaosvmProofs.Definitions.Helpers

/-! # Q avalanche function (Rust: `g_mixer.rs:37`).

Concrete implementation matching Rust `q_avalanche`:
  z = x.wrapping_mul(p.mult);  // mod 2^64
  z ^= z >> p.xor_shift;       // shr followed by XOR
  z.rotate_left(p.rot)         // 64-bit rotation
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
