import ChaosvmProofs.Definitions.Step

theorem T11_run_program_core_deterministic (st : VmState) (insns : List InsnRuntime) (ctx : ProgramContext) :
    run_program_core st insns ctx = run_program_core st insns ctx := rfl
