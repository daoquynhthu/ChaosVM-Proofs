import ChaosvmProofs.Definitions.SemShare
import ChaosvmProofs.Definitions.PhiPerm

/-- T08a: bridge+decode invariant with full permute (QAvalanche-backed).
    For any σ,DDM,c1,anchor,c2,q_sigma,q_ddm: decode(bridge(encode(op))) = op.
    This proves the v_t-level roundtrip (before phi_op_inv).
    Full proof in Definitions/SemShare.lean. -/
theorem T08_bridge_decode_invariant (u anchor c1_t c2 σ DDM : Nat) (q_sigma q_ddm : QAvalancheConfig) :
    decode_i41 (bridge_i41 (encode_c0_i41 u anchor c2 q_sigma q_ddm) anchor c1_t c2 σ DDM q_sigma q_ddm)
               c1_t c2 σ DDM q_sigma q_ddm = u :=
  bridge_decode_invariant u anchor c1_t c2 σ DDM q_sigma q_ddm

/-- T08b: full roundtrip (including phi_op_inv).
    decode(bridge(encode(phi(op)))) with phi_op_inv applied → original op.
    This proves the Rust-level roundtrip where `phi_op_inv[v_t] = original_op`. -/
theorem T08_full_roundtrip (op anchor c1_t c2 σ DDM : Nat)
    (q_sigma q_ddm : QAvalancheConfig) (hop : op < 256) :
    decode_full (bridge_i41 (encode_c0_i41 (phi op) anchor c2 q_sigma q_ddm)
                 anchor c1_t c2 σ DDM q_sigma q_ddm)
                c1_t c2 σ DDM q_sigma q_ddm = op :=
  full_bridge_decode_invariant op anchor c1_t c2 σ DDM q_sigma q_ddm hop

/-- T08c: per-step full roundtrip (including phi_op_inv_step).
    decode_full_step(bridge(encode(phi_op_step(op)))) → original op.
    This proves the Rust-level roundtrip where `phi_op_inv_step(v_t, σ, DDM, H) = original_op`. -/
theorem T08_full_roundtrip_step (op anchor c1_t c2 σ DDM H : Nat)
    (q_sigma q_ddm q_op : QAvalancheConfig) (hop : op < 256) :
    decode_full_step
      (bridge_i41 (encode_c0_i41 (phi_op_step op σ DDM H q_op) anchor c2 q_sigma q_ddm)
                   anchor c1_t c2 σ DDM q_sigma q_ddm)
      c1_t c2 σ DDM H q_sigma q_ddm q_op = op :=
  full_bridge_decode_invariant_step op anchor c1_t c2 σ DDM H q_sigma q_ddm q_op hop
