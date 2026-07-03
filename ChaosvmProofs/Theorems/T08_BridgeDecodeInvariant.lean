import ChaosvmProofs.Definitions.SemShare

/-- T08: bridge+decode invariant with full permute (QAvalanche-backed).
    For any σ,DDM,c1,anchor,c2,q_sigma,q_ddm: decode(bridge(encode(op))) = op.
    Full proof in Definitions/SemShare.lean. -/
theorem T08_bridge_decode_invariant (u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2 q_sigma q_ddm) anchor c1_t c2 σ DDM q_sigma q_ddm)
               c1_t c2 σ DDM q_sigma q_ddm = u :=
  bridge_decode_invariant u anchor c1_t c2 σ DDM q_sigma q_ddm
