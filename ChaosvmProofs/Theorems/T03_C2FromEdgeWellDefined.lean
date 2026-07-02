import ChaosvmProofs.Definitions.EdgeEncoding

/-- T03: c2_from_edge always returns a value < 256.
    Proof in Definitions/EdgeEncoding.lean. -/
theorem T03_c2_edge_lt_256 (edge : Nat) : c2_from_edge edge < 256 :=
  c2_from_edge_byte edge
