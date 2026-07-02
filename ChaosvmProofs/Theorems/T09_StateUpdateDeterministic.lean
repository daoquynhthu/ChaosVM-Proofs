import ChaosvmProofs.Definitions.StateUpdate

theorem T09_update_state_deterministic (σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt : Nat)
    (q_h q_sigma q_cfa q_ddm : QAvalancheConfig) :
    update_state σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt q_h q_sigma q_cfa q_ddm =
    update_state σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt q_h q_sigma q_cfa q_ddm :=
  update_state_deterministic σ CFA DDM h z_lo z_hi ra_val rb_val result edge mem call spawn ent_mix ctr r0 salt q_h q_sigma q_cfa q_ddm
