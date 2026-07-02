# T01: P(x,s) Bijective on u8

## Statement

For any `a, b : ℕ` with `a % 2 = 1` (a odd), the function `λ x : ℕ ⇒ (a·x + b) % 256` is a bijection on `{0, ..., 255}`.

Equivalently: `P_mod : ℕ → ℕ → ℕ → ℕ` is bijective in its first argument when the second argument is odd.

## Rust Source

`chaosvm-core/src/conj_vm/sem_share.rs:56-60`

```rust
pub fn permute(val: u8, state: u64, q: &QAvalanche) -> u8 {
    let mix = q_avalanche(state, q);
    let a = (mix as u8) | 1; // always odd → bijective
    let b = (mix >> 8) as u8;
    a.wrapping_mul(val).wrapping_add(b)
}
```

## Formal Details

- **Domain**: ℤ₂₅₆ (represented as `{x : ℕ | x < 256}`)
- **Map**: `P(x) = a·x + b mod 256`, with `a` odd, `b` arbitrary
- **Key lemma**: `gcd(a, 256) = 1` when `a` is odd
- **Inverse**: `P⁻¹(y) = a⁻¹·(y - b) mod 256` where `a·a⁻¹ ≡ 1 (mod 256)`

## Proof Strategy

1. Show that `a` odd ⇒ `gcd a 256 = 1` (using the Euclidean algorithm: 256 = 2⁸, so any odd number has no common factor with 256)
2. Show that `gcd a 256 = 1` ⇒ `a` has a multiplicative inverse `a⁻¹` modulo 256
3. Show that `P(x) = P(x')` ⇒ `x = x'` (injectivity)
4. Show that for any `y`, `P(a⁻¹·(y-b) mod 256) = y` (surjectivity)

## Dependencies

- None (single-variable, only uses arithmetic modulo 256)
- Lean needed: `Nat.gcd`, `Nat.xgcd`, modular arithmetic

## Lean File

`ChaosvmProofs/Definitions/Permutation.lean`
