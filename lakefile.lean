import Lake
open Lake DSL

package ChaosvmProofs where
  -- Formal proofs for ChaosVM v2 Φₜ dynamic conjugate VM.
  --
  -- To build: `lake build` (requires Lean 4 v4.12.0+)
  -- To test:  `lake test`
  --
  -- Directory structure:
  --   ChaosvmProofs/Definitions/  — formalisation of VM primitives
  --   ChaosvmProofs/Theorems/     — verified theorem proofs
  --   targets/                    — proof target blueprints (markdown)

@[default_target]
lean_lib ChaosvmProofs
