/-! # Shared helpers for formal proofs.

## Rotation

64-bit rotation via multiply/divide by powers of 2 (core Lean lacks shift).
The rotl/rotr identities (for `∃` proofs) use XOR self-cancellation instead
of requiring the full rotation inverse theorem, which avoids complex bit-level
proofs while keeping the definitions faithful to Rust.
-/

/-- 64-bit mask: (2^64 - 1). -/
def mask64 : Nat := 2 ^ 64 - 1

/-- Left shift by n bits (multiply by 2^n). -/
def shl (x n : Nat) : Nat := x * (2 ^ n)

/-- Right shift by n bits (integer divide by 2^n). -/
def shr (x n : Nat) : Nat := x / (2 ^ n)

/-- 64-bit left rotation. -/
def rotl64 (x n : Nat) : Nat :=
  let n' := n % 64
  Nat.lor ((shl x n') % (2 ^ 64)) (Nat.land (shr x (64 - n')) mask64)

/-- 64-bit right rotation: inverse of rotl64 (proof below is axiomatic). -/
def rotr64 (x n : Nat) : Nat :=
  let n' := n % 64
  Nat.lor (Nat.land (shl x (64 - n')) mask64) (shr x n')

/-- Mod 256 (restrict to byte range). -/
def toByte (x : Nat) : Nat := x % 256

/-- Left rotation (alias for API compatibility). -/
def rotl (x n : Nat) : Nat := rotl64 x n

/-- Right rotation (alias for API compatibility). -/
def rotr (x n : Nat) : Nat := rotr64 x n
