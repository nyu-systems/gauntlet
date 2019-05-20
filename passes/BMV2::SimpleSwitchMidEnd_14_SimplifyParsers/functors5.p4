*** dumps/p4_16_samples/functors5.p4/pruned/functors5-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:58:24.037469400 +0200
--- dumps/p4_16_samples/functors5.p4/pruned/functors5-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:58:24.042202400 +0200
*************** package m(simple n);
*** 4,16 ****
  parser p2_0(out bit<2> w) {
      bit<2> w_1;
      state start {
-         transition p1_0_start;
-     }
-     state p1_0_start {
          w_1 = 2w2;
-         transition start_0;
-     }
-     state start_0 {
          w = w_1;
          transition accept;
      }
--- 4,10 ----
