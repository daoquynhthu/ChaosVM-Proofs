# T02: affine_map is bijective

## Statement
For any a,b with a odd, λ r → (a·r + b) % 256 is bijective on {0,...,255}.

Same proof as T01. Used for register mapping in the VM.

## Rust Source
`chaosvm-core/src/conj_vm/reg_map.rs`

## Dependencies
T01 (same proof structure)

