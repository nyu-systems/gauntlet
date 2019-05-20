*** dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:57.822626800 +0200
--- dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:57.828971000 +0200
*************** control c(inout Headers h, inout standar
*** 29,37 ****
          default_action = NoAction_0();
      }
      apply {
!         {
!             tns.apply();
!         }
      }
  }
  parser p<H>(packet_in _p, out H h);
--- 29,35 ----
          default_action = NoAction_0();
      }
      apply {
!         tns.apply();
      }
  }
  parser p<H>(packet_in _p, out H h);
