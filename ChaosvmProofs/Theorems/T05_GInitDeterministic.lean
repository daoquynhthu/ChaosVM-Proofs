import ChaosvmProofs.Definitions.GMixer

theorem T05_gInit_deterministic (tS tC tD σ CFA DDM h r0 r1 : Nat) :
    gInit tS tC tD σ CFA DDM h r0 r1 = gInit tS tC tD σ CFA DDM h r0 r1 :=
  gInit_deterministic tS tC tD σ CFA DDM h r0 r1
