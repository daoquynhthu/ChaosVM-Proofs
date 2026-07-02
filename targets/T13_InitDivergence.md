# T13: Init diverges with poison

## Statement
(pσ≠0 ∨ pC≠0 ∨ pD≠0) → init_poisoned(...) ≠ init(...)

## Rust Source
`chaosvm-core/src/conj_vm/init.rs:158-200`

## Strategy
Show at least one state field differs when poison is non-zero.

## Status
Proof not yet complete in Init.lean

