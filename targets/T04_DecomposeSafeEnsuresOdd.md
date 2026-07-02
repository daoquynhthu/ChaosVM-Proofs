# T04: decompose_safe ensures odd multipliers

## Statement
∀ z_lo, z_hi:
  (decompose_safe z_lo z_hi).a_rd % 2 = 1 ∧
  (decompose_safe z_lo z_hi).a_ra % 2 = 1 ∧
  (decompose_safe z_lo z_hi).a_rb % 2 = 1

## Rust Source
`chaosvm-core/src/conj_vm/z_layout.rs:64-75`

## Status
✅ Proved in ZLayout.lean

