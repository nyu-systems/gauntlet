*** dumps/p4_16_samples/functors3.p4/pruned/functors3-BMV2::SimpleSwitchMidEnd_9_ConstantFolding.p4	2019-05-20 16:58:23.483658000 +0200
--- dumps/p4_16_samples/functors3.p4/pruned/functors3-BMV2::SimpleSwitchMidEnd_10_StrengthReduction.p4	2019-05-20 16:58:23.371247000 +0200
*************** parser p_0(out bit<1> z) {
*** 12,18 ****
      }
      state start_0 {
          z = z1;
!         z = z & 1w0 & 1w1;
          transition accept;
      }
  }
--- 12,18 ----
      }
      state start_0 {
          z = z1;
!         z = 1w0;
          transition accept;
      }
  }
