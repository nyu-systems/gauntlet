*** dumps/p4_16_samples/key1-bmv2.p4/pruned/key1-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:43.734066400 +0200
--- dumps/p4_16_samples/key1-bmv2.p4/pruned/key1-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:43.736878500 +0200
*************** control ingress(inout Headers h, inout M
*** 50,59 ****
          default_action = NoAction_0();
      }
      apply {
!         {
!             key_0 = h.h.a + 32w1;
!             c_t_0.apply();
!         }
          sm.egress_spec = 9w0;
      }
  }
--- 50,57 ----
          default_action = NoAction_0();
      }
      apply {
!         key_0 = h.h.a + 32w1;
!         c_t_0.apply();
          sm.egress_spec = 9w0;
      }
  }
