import ChaosvmProofs.Definitions.SemShare

/-- T08: bridge+decode invariant. For any σ,DDM,c1,anchor,c2:
    decode(bridge(encode(op))) = op.
    Full proof in Definitions/SemShare.lean. -/
theorem T08_bridge_decode_invariant (u anchor c1_t c2 σ DDM : Nat) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2) anchor c1_t c2 σ DDM) c1_t c2 σ DDM = u :=
  bridge_decode_invariant u anchor c1_t c2 σ DDM
