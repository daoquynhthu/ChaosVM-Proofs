import ChaosvmProofs.Definitions.Step

theorem T10_step_core_deterministic (sigma cfa ddm h pc ctr ctx_digest
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
