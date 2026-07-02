# T10: step() is deterministic

## Statement
step() is a pure function: same (state, insn, tables, config) → same output.

## Rust Source
`chaosvm-core/src/conj_vm/exec.rs:720-999`

## Dependencies
T05, T06, T08, T09

