import ChaosvmProofs.Definitions.Helpers
import ChaosvmProofs.Definitions.QAvalanche
import ChaosvmProofs.Definitions.GMixer
import ChaosvmProofs.Definitions.HIndex
import ChaosvmProofs.Definitions.ZLayout
import ChaosvmProofs.Definitions.EdgeEncoding
import ChaosvmProofs.Definitions.SemShare
import ChaosvmProofs.Definitions.StateUpdate

/-- Subset of VmState that changes across steps. -/
structure VmState where
  sigma      : Nat
  cfa        : Nat
  ddm        : Nat
  h          : Nat
  pc         : Nat
  ctr        : Nat
  ctx_digest : Nat

/-- Constant program parameters (tables, configs, run nonces). -/
structure ProgramContext where
  t_sigma  : Nat → Nat
  t_cfa    : Nat → Nat
  t_ddm    : Nat → Nat
  g_config : GMixerConfig
  q_sigma  : QAvalancheConfig
  q_cfa    : QAvalancheConfig
  q_ddm    : QAvalancheConfig
  q_h      : QAvalancheConfig
  q_ent    : QAvalancheConfig
  r0       : Nat
  r1       : Nat
  m        : Nat

/-- Per-instruction runtime data extracted from registers/memory. -/
structure InsnRuntime where
  alpha   : Nat
  c0      : Nat
  edge    : Nat
  ra_val  : Nat
  rb_val  : Nat
  result  : Nat
  mem_val : Nat
  call    : Nat
  spawn   : Nat
  ent_mix : Nat
  salt    : Nat

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
  let c0_eff := bridge_i41 c0 anchor c1_t c2 sigma ddm q_sigma q_ddm
  let v_t    := decode_i41 c0_eff c1_t c2 sigma ddm q_sigma q_ddm
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

/-- Run one step given structured state/instruction/context.
    Returns (next_state, result). -/
def step_once (st : VmState) (insn : InsnRuntime) (ctx : ProgramContext) : VmState × Nat :=
  let so := step_core st.sigma st.cfa st.ddm st.h st.pc st.ctr st.ctx_digest
              insn.edge insn.alpha insn.c0 ctx.r0 ctx.r1 ctx.m
              ctx.t_sigma ctx.t_cfa ctx.t_ddm ctx.g_config
              ctx.q_sigma ctx.q_cfa ctx.q_ddm ctx.q_h ctx.q_ent
              insn.ra_val insn.rb_val insn.result insn.mem_val insn.call insn.spawn insn.ent_mix insn.salt
  let next : VmState := {
    sigma      := so.sigma_next
    cfa        := so.cfa_next
    ddm        := so.ddm_next
    h          := so.h_next
    pc         := so.pc_next
    ctr        := so.ctr_next
    ctx_digest := so.ctx_digest_next
  }
  (next, so.v_t)

/-- Iterate step_once over a list of instruction frames.
    Returns (final_state, accumulated_results). -/
def run_program_core (st : VmState) (insns : List InsnRuntime) (ctx : ProgramContext) : VmState × List Nat :=
  match insns with
  | [] => (st, [])
  | frame :: rest =>
    let (st', res) := step_once st frame ctx
    let (st'', results) := run_program_core st' rest ctx
    (st'', res :: results)

/-- step_core is deterministic: equal inputs → equal outputs. -/
theorem step_core_deterministic (sigma cfa ddm h pc ctr ctx_digest
                                edge alpha c0 r0 r1 m : Nat)
                               (t_sigma t_cfa t_ddm : Nat → Nat)
                               (g_config : GMixerConfig)
                               (q_sigma q_cfa q_ddm q_h q_ent : QAvalancheConfig)
                               (ra_val rb_val result mem_val call spawn ent_mix salt : Nat) :
    step_core sigma cfa ddm h pc ctr ctx_digest
              edge alpha c0 r0 r1 m
              t_sigma t_cfa t_ddm g_config
              q_sigma q_cfa q_ddm q_h q_ent
              ra_val rb_val result mem_val call spawn ent_mix salt =
    step_core sigma cfa ddm h pc ctr ctx_digest
              edge alpha c0 r0 r1 m
              t_sigma t_cfa t_ddm g_config
              q_sigma q_cfa q_ddm q_h q_ent
              ra_val rb_val result mem_val call spawn ent_mix salt := rfl

/-- run_program_core is deterministic: equal inputs → equal outputs. -/
theorem run_program_core_deterministic (st : VmState) (insns : List InsnRuntime) (ctx : ProgramContext) :
    run_program_core st insns ctx = run_program_core st insns ctx := rfl
