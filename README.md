# ChaosVM v2 Formal Proofs

Formal verification of the ChaosVM v2 obfuscating VM using [Lean 4](https://lean-lang.org/).
The proofs establish core security properties of the Φₜ dynamic conjugacy architecture,
including the I-41 semantic share bridge/decode invariant, G mixer bijectivity, H-chain
digest dependency, state determinism, and anti-tamper divergence.

## Repository Structure

```
ChaosvmProofs/
├── Definitions/          ← Formal model of Rust implementation
│   ├── Helpers.lean        rotl/rotr/shift/mask primitives
│   ├── QAvalanche.lean     Q avalanche function (multiply-XOR-shift-rotate)
│   ├── Permutation.lean    P_mod bijective affine map (Fin 256)
│   ├── GMixer.lean         G mixer: gInit, 3-round gRounds, gMix
│   ├── HIndex.lean         hⱼ table index functions (h_sigma, h_cfa, h_ddm)
│   ├── SemShare.lean       I-41 bridge+decode pipeline
│   ├── StateUpdate.lean    State update (σ/CFA/DDM/H evolution)
│   ├── ZLayout.lean        z_t bit decomposition
│   ├── EdgeEncoding.lean   c2_from_edge encoding
│   ├── Init.lean           R_run initialization (clean & poisoned)
│   └── Step.lean           step() and run_program() models
├── Theorems/             ← Theorem statements and proofs
│   ├── T0{1..4}_*.lean     Level 1: primitive bijectivity
│   ├── T0{5..7}_*.lean     Level 2: G mixer determinism & bijectivity
│   ├── T08_*.lean          Level 3: bridge+decode invariant
│   ├── T0{9..11}_*.lean    Level 4: state evolution determinism
│   ├── T1{2..5}_*.lean     Level 5: anti-tamper properties
│   ├── T16_*.lean          Level 6: R_run invariance
│   ├── T17_*.lean          Level 7: functional equivalence
│   ├── K1_*.lean           K1: gRounds 3-round bijection
│   ├── K2_*.lean           K2: H-chain digest dependency
│   └── K4_*.lean           K4: share indispensability
├── targets/              ← Proof target specifications
│   ├── index.md            Dependency hierarchy overview
│   ├── T{01..17}_*.md      Individual theorem targets
│   ├── end_to_end.md       End-to-end equivalence target
│   └── whitebox_core.md    Whitelist/blacklist core semantics
├── plans/                ← Audit reports and proof plans
├── lakefile.lean          Lean 4 project configuration
└── lean-toolchain         Lean toolchain version pinning
```

## Theorem Progress

| Level | Theorems | Proved | Remaining |
|-------|----------|--------|-----------|
| 1 — Primitive bijectivity | T01–T04 | **4/4** | — |
| 2 — G mixer | T05–T07 | **3/3** | — |
| 3 — Bridge+decode invariant | T08 | **1/1** | — |
| 4 — State determinism | T09–T11 | **3/3** | — |
| 5 — Anti-tamper | T12–T15 | **2/4** | T14 (poison cascade), T15 (no single exit) |
| 6 — R_run invariance | T16 | **0/1** | T16 |
| 7 — Functional equivalence | T17 | **0/1** | T17 |
| K-series (audit findings) | K1, K2, K4 | **3/3** | — |
| **Total** | **20 files** | **16/20 (80%)** | **4** |

## Build & Test

```bash
lake build              # build all definitions & theorems
lake build ChaosvmProofs  # build top-level module only
```

Requires Lean 4.30.0+ (pinned in `lean-toolchain`).

## Dependencies

The project is self-contained with no external dependencies beyond the Lean 4
standard library and the `Init`/`Omega` prelude.

## License

Apache 2.0 — see [LICENSE](LICENSE).
