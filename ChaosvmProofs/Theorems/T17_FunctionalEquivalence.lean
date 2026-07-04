import ChaosvmProofs.Definitions.SemShare
import ChaosvmProofs.Definitions.PhiPerm
import ChaosvmProofs.Definitions.Step

set_option maxHeartbeats 50000000

/-- XOR left cancellation: `a ^^^ b = a ^^^ c` → `b = c`. -/
theorem xor_left_cancel (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  calc
    b = (a ^^^ a) ^^^ b := by simp
    _ = a ^^^ (a ^^^ b) := by rw [Nat.xor_assoc]
    _ = a ^^^ (a ^^^ c) := by rw [h]
    _ = (a ^^^ a) ^^^ c := by rw [Nat.xor_assoc]
    _ = c := by simp

/-- XOR left commutativity: `a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c)`. -/
theorem xor_left_comm (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  calc
    a ^^^ (b ^^^ c) = (a ^^^ b) ^^^ c := by rw [← Nat.xor_assoc]
    _ = (b ^^^ a) ^^^ c := by rw [Nat.xor_comm a b]
    _ = b ^^^ (a ^^^ c) := by rw [Nat.xor_assoc]

/-- Step 1: `v_t` is independent of σ, DDM, c1_t — the permute terms cancel pairwise.
    `decode(bridge(c0, anchor, c1_t, c2, σ, DDM, qσ, qD), c1_t, c2, σ, DDM, qσ, qD)`
    = `c0 ^^^ permute(anchor, 0, qσ) ^^^ permute(c2, 0, qD)`. -/
theorem decode_bridge_independent (c0 anchor c2 : Nat) (q_sigma q_ddm : QAvalancheConfig) :
    ∀ (c1_t σ DDM : Nat),
    decode_i41 (bridge_i41 c0 anchor c1_t c2 σ DDM q_sigma q_ddm) c1_t c2 σ DDM q_sigma q_ddm
    = c0 ^^^ permute anchor 0 q_sigma ^^^ permute c2 0 q_ddm := by
  intro c1_t σ DDM
  unfold decode_i41 bridge_i41
  let C := permute c1_t σ q_sigma
  let A := permute anchor 0 q_sigma
  let D := permute c2 DDM q_ddm
  let B := permute c2 0 q_ddm
  have hCD : C ^^^ D ^^^ B ^^^ C ^^^ D = B := by
    simpa [Nat.xor_assoc] using swap_pair (C ^^^ D) B
  calc
    c0 ^^^ C ^^^ A ^^^ D ^^^ B ^^^ C ^^^ D
        = c0 ^^^ A ^^^ (C ^^^ D ^^^ B ^^^ C ^^^ D) := by
          simp [Nat.xor_assoc, Nat.xor_comm, xor_left_comm]
    _ = c0 ^^^ A ^^^ B := by rw [hCD]

/-- Step 2: step_once produces the same v_t for any two states. -/
theorem step_once_v_t_invariant (st₁ st₂ : VmState) (insn : InsnRuntime) (ctx : ProgramContext) :
    (step_once st₁ insn ctx).snd = (step_once st₂ insn ctx).snd := by
  unfold step_once
  have h_v_eq : ∀ (sigma cfa ddm h pc ctr ctx_digest : Nat),
      (step_core sigma cfa ddm h pc ctr ctx_digest
                insn.edge insn.alpha insn.c0 ctx.r0 ctx.r1 ctx.m
                ctx.t_sigma ctx.t_cfa ctx.t_ddm ctx.g_config
                ctx.q_sigma ctx.q_cfa ctx.q_ddm ctx.q_h ctx.q_ent
                insn.ra_val insn.rb_val insn.result insn.mem_val insn.call insn.spawn insn.ent_mix insn.salt).v_t
      = insn.c0 ^^^ permute (ctx.t_ddm insn.alpha % 256) 0 ctx.q_sigma
                 ^^^ permute (c2_from_edge insn.edge) 0 ctx.q_ddm := by
    intro sigma cfa ddm h pc ctr ctx_digest
    unfold step_core
    dsimp
    apply decode_bridge_independent insn.c0 (ctx.t_ddm insn.alpha % 256) (c2_from_edge insn.edge)
                                     ctx.q_sigma ctx.q_ddm
                                     (ctx.t_ddm (h_ddm pc ctx.m ddm sigma cfa h ctx.q_ddm) % 256)
                                     sigma ddm
  simp [h_v_eq (st₁.sigma) (st₁.cfa) (st₁.ddm) (st₁.h) (st₁.pc) (st₁.ctr) (st₁.ctx_digest),
        h_v_eq (st₂.sigma) (st₂.cfa) (st₂.ddm) (st₂.h) (st₂.pc) (st₂.ctr) (st₂.ctx_digest)]

/-- Step 3: Main theorem — functional equivalence across any two initial states.
    The output trace (list of decoded opcodes) depends only on the instructions
    and the program context, not on the internal VM state (and thus not on R_run). -/
theorem T17_functional_equivalence (st₁ st₂ : VmState) (insns : List InsnRuntime) (ctx : ProgramContext) :
    (run_program_core st₁ insns ctx).snd = (run_program_core st₂ insns ctx).snd := by
  induction insns generalizing st₁ st₂ with
  | nil => rfl
  | cons frame rest ih =>
    have hv : (step_once st₁ frame ctx).snd = (step_once st₂ frame ctx).snd :=
      step_once_v_t_invariant st₁ st₂ frame ctx
    have h_rest : (run_program_core (step_once st₁ frame ctx).fst rest ctx).snd
               = (run_program_core (step_once st₂ frame ctx).fst rest ctx).snd :=
      ih (step_once st₁ frame ctx).fst (step_once st₂ frame ctx).fst
    have h_left : (run_program_core st₁ (frame :: rest) ctx).snd =
        (step_once st₁ frame ctx).snd :: (run_program_core (step_once st₁ frame ctx).fst rest ctx).snd := by
      simp [run_program_core, step_once]
    have h_right : (run_program_core st₂ (frame :: rest) ctx).snd =
        (step_once st₂ frame ctx).snd :: (run_program_core (step_once st₂ frame ctx).fst rest ctx).snd := by
      simp [run_program_core, step_once]
    calc
      (run_program_core st₁ (frame :: rest) ctx).snd
          = (step_once st₁ frame ctx).snd :: (run_program_core (step_once st₁ frame ctx).fst rest ctx).snd := h_left
      _ = (step_once st₂ frame ctx).snd :: (run_program_core (step_once st₂ frame ctx).fst rest ctx).snd := by
        rw [hv, h_rest]
      _ = (run_program_core st₂ (frame :: rest) ctx).snd := h_right.symm

/-- T17 full: 完整解码输出（经过 phi_op_inv 置换）对任意两组初始状态相同。
    即 Rust 的 `phi_op_inv[v_t]`（实际 opcode）不依赖于 VM 内部状态。 -/
theorem T17_functional_equivalence_full (st₁ st₂ : VmState)
    (insns : List InsnRuntime) (ctx : ProgramContext) :
    List.map decode_full (run_program_core st₁ insns ctx).snd =
    List.map decode_full (run_program_core st₂ insns ctx).snd := by
  have h := T17_functional_equivalence st₁ st₂ insns ctx
  rw [h]
