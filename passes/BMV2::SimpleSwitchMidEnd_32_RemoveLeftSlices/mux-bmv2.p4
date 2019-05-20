*** dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 16:59:47.527541200 +0200
--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 16:59:47.532107300 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 21,27 ****
          val = res;
          tmp_0 = res[31:0];
          tmp_0 = tmp_0;
!         val[31:0] = tmp_0;
          res = val;
      }
      apply {
--- 21,27 ----
          val = res;
          tmp_0 = res[31:0];
          tmp_0 = tmp_0;
!         val = val & ~64w0xffffffff | (bit<64>)tmp_0 << 0 & 64w0xffffffff;
          res = val;
      }
      apply {
