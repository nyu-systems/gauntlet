*** dumps/p4_16_samples/exit4.p4/pruned/exit4-BMV2::SimpleSwitchMidEnd_30_CompileTimeOperations.p4	2019-05-20 16:58:18.355771600 +0200
--- dumps/p4_16_samples/exit4.p4/pruned/exit4-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 16:58:18.358667500 +0200
*************** control ctrl() {
*** 10,16 ****
          default_action = e_0();
      }
      apply {
!         tmp_0 = t.apply().hit;
          if (tmp_0) 
              t.apply();
          else 
--- 10,19 ----
          default_action = e_0();
      }
      apply {
!         if (t.apply().hit) 
!             tmp_0 = true;
!         else 
!             tmp_0 = false;
          if (tmp_0) 
              t.apply();
          else 
