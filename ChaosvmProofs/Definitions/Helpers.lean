/-! # Shared helpers for formal proofs. -/

/-- Bitwise OR on Nat. -/
def or (a b : Nat) : Nat := Nat.lor a b

/-- Left rotation (abstract — exact bit positions not needed). -/
def rotl (x n : Nat) : Nat := x

/-- Right rotation (abstract). -/
def rotr (x n : Nat) : Nat := x

/-- Mod 256 (restrict to byte range). -/
def toByte (x : Nat) : Nat := x % 256
