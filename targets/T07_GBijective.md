# T07: G mixer is bijective

## Statement
For any fixed GMixerConfig, the map (x,y,w) → (z_lo, z_hi) from gRounds is injective.

## Rust Source
`chaosvm-core/src/conj_vm/g_mixer.rs:63-97`

## Proof Strategy
1. Each ARX round is invertible (trace backwards from output)
2. Each Q avalanche is bijective (multiply-by-odd → xor-shift → rotate)
3. 3-round composition is bijective

## Dependencies
T01, q_avalanche bijectivity

## Difficulty
Hardest primitive theorem.

