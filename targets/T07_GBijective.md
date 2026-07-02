# T07a + T07b: G mixer formal properties (replaces original T07)

## Background

The original T07 claimed "G mixer is bijective (x,y,w)→(z_lo,z_hi)". This is
**mathematically impossible**: (x,y,w) = 192 bits, (z_lo,z_hi) = 128 bits.
A function from a larger to a smaller domain cannot be injective.

The 64-bit compression is an **intentional entropy-hiding design feature**,
not a bug. The output mixing prevents full state recovery by an attacker.

## T07a: ARX+Q rounds are a permutation on (x,y,w)

Each round consists of 6 substeps, each individually invertible:
1. `x ← x + rotl(y⊕k, a)`    → invert: `x = x' - rotl(y⊕k, a)`
2. `y ← y ⊕ rotl(w+k', b)`   → invert: XOR is self-inverse
3. `w ← w + rotl(x⊕k'', c)`  → invert: `w = w' - rotl(x⊕k'', c)`
4. `x ← x ⊕ Q(y)`            → invert: XOR is self-inverse
5. `y ← y + Q(w)`            → invert: `y = y' - Q(w)`
6. `w ← w ⊕ Q(x)`            → invert: XOR is self-inverse

3 rounds = composition of 3 bijections = bijection.

**Status**: ✅ Proved in GMixer.lean (step_a_bij, step_b_bij, step_c_bij,
qsub_x_bij, qsub_y_bij, round_bijection)

## T07b: Output mixing is surjective

The map `(x,y,w) → (x⊕rotl(y,23), w⊕rotl(x,41))` is onto ℤ₂₅₆².

For any (z_lo, z_hi), choose x=0, y=rotr(z_lo,23), w=z_hi:
- `0 ⊕ rotl(rotr(z_lo,23), 23) = z_lo` ✓
- `z_hi ⊕ rotl(0, 41) = z_hi` ✓

**Status**: ✅ Proved in GMixer.lean (output_mixing_surjective)

## Dependencies
- T01 (odd a ensures bijectivity) — used conceptually but not directly called
- Basic Nat arithmetic (addition, subtraction, XOR)

## Lean File
`ChaosvmProofs/Definitions/GMixer.lean`
