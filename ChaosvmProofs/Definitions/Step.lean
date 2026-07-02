import ChaosvmProofs.Definitions.Helpers
import ChaosvmProofs.Definitions.QAvalanche
import ChaosvmProofs.Definitions.GMixer
import ChaosvmProofs.Definitions.HIndex
import ChaosvmProofs.Definitions.ZLayout
import ChaosvmProofs.Definitions.EdgeEncoding
import ChaosvmProofs.Definitions.SemShare
import ChaosvmProofs.Definitions.StateUpdate

/-- Result of one step() invocation.  Models Rust `VmState` fields that change. -/
structure StepOutput where
  sigma_next     : Nat
  cfa_next       : Nat
  ddm_next       : Nat
  h_next         : Nat
  pc_next        : Nat
  ctr_next       : Nat
  ctx_digest_next : Nat
  v_t            : Nat
  z_lo           : Nat
  z_hi           : Nat

/-- Core step() pipeline without branch entanglement or control-flow dispatch.

    Matches Rust `exec.rs:720–999` at the functional level:
      1. h_j table indices
      2. G mixer → (z_lo, z_hi)
      3. decompose_safe → ZFields
      4. I-41 bridge+decode → v_t
      5. update_state → new σ/CFA/DDM/H
      6. Advance pc/ctr/ctx_digest

    Parameters match the Rust `step()` signature minus &VmState (flattened),
    &EncodedInsn (flattened), and the redundant `q_poison`/`phi_op_inv`/
    `base_key`/`branches` (abstracted away for the deterministic model).
 -/
def step_core (sigma cfa ddm h pc ctr ctx_digest
               edge alpha c0 r0 r1 m : Nat)
              (t_sigma t_cfa t_ddm : Nat → Nat)
              (g_config : GMixerConfig)
              (q_sigma q_cfa q_ddm q_h q_ent : QAvalancheConfig)
              (ra_val rb_val result mem_val call spawn ent_mix salt : Nat)
              : StepOutput :=
  let i_s    := h_sigma  pc          sigma h  r0  q_sigma
  let i_c    := h_cfa   edge         cfa   h  ctr r1   q_cfa
  let j_t    := h_ddm   pc  m        ddm sigma cfa h   q_ddm
  let td_entry := t_ddm j_t
  let c1_t   := td_entry % 256
  let anchor := t_ddm alpha % 256
  let (x, y, w) := gInit (t_sigma i_s) (t_cfa i_c) td_entry sigma cfa ddm h r0 r1
  let (z_lo, z_hi) := gRounds x y w g_config
  let zf     := decompose_safe z_lo z_hi
  let c2     := c2_from_edge edge
  let c0_eff := bridge_i41 c0 anchor c1_t c2 sigma ddm
  let v_t    := decode_i41 c0_eff c1_t c2 sigma ddm
  let result_for_su := result ^^^ Nat.lor (shl zf.sem_decomp 8) zf.ctrl_edge_perm
  let ns := update_state sigma cfa ddm h z_lo z_hi ra_val rb_val
              result_for_su edge mem_val call spawn ent_mix ctr r0 salt
              q_h q_sigma q_cfa q_ddm
  let pc_next  := pc + 1
  let ctr_next := ctr + 1
  let ctx_digest_next := qAvalanche (ctx_digest ^^^ ns.h_next ^^^ result_for_su) q_ent
  {
    sigma_next  := ns.sigma_next
    cfa_next    := ns.cfa_next
    ddm_next    := ns.ddm_next
    h_next      := ns.h_next
    pc_next     := pc_next
    ctr_next    := ctr_next
    ctx_digest_next := ctx_digest_next
    v_t         := v_t
    z_lo        := z_lo
    z_hi        := z_hi
  }
