import ChaosvmProofs.Definitions.Init

theorem T12_init_deterministic (k0 k1 r0 r1 : Nat) (qσ qC qD qH : QAvalancheConfig) :
    init k0 k1 r0 r1 qσ qC qD qH = init k0 k1 r0 r1 qσ qC qD qH :=
  init_deterministic k0 k1 r0 r1 qσ qC qD qH
