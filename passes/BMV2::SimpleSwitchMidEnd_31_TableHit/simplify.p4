*** dumps/p4_16_samples/simplify.p4/pruned/simplify-BMV2::SimpleSwitchMidEnd_30_CompileTimeOperations.p4	2019-05-20 17:00:22.223278900 +0200
--- dumps/p4_16_samples/simplify.p4/pruned/simplify-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:00:22.225719500 +0200
*************** control c(out bool x) {
*** 27,37 ****
      }
      apply {
          x = true;
!         tmp_2 = t1.apply().hit;
          if (!tmp_2) 
              tmp_3 = false;
          else {
!             tmp_4 = t2.apply().hit;
              tmp_3 = tmp_4;
          }
          if (tmp_3) 
--- 27,43 ----
      }
      apply {
          x = true;
!         if (t1.apply().hit) 
!             tmp_2 = true;
!         else 
!             tmp_2 = false;
          if (!tmp_2) 
              tmp_3 = false;
          else {
!             if (t2.apply().hit) 
!                 tmp_4 = true;
!             else 
!                 tmp_4 = false;
              tmp_3 = tmp_4;
          }
          if (tmp_3) 
