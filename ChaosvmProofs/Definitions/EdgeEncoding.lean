import ChaosvmProofs.Definitions.Helpers

/-! # Edge encoding (Rust: `edge_encoding.rs`). -/

/-- c2 = (edge ⊕ (edge>>8) ⊕ (edge>>16)) % 256 (Rust: `c2_from_edge`). -/
def c2_from_edge (edge : Nat) : Nat :=
  (edge ^^^ (edge / 256) ^^^ (edge / 65536)) % 256

/-- Assign edge labels (abstract). -/
def assign_edge_labels (num : Nat) (seed : Nat) : List Nat :=
  List.range num

theorem c2_from_edge_deterministic (edge : Nat) : c2_from_edge edge = c2_from_edge edge := rfl

theorem c2_from_edge_byte (edge : Nat) : c2_from_edge edge < 256 := by
  unfold c2_from_edge
  exact Nat.mod_lt _ (by decide)
