*** dumps/p4_16_samples/functors4.p4/pruned/functors4-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:58:23.711066000 +0200
--- dumps/p4_16_samples/functors4.p4/pruned/functors4-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:58:23.714275600 +0200
***************
*** 2,14 ****
  parser p(out bit<1> z) {
      bit<1> z1;
      state start {
-         transition p1_0_start;
-     }
-     state p1_0_start {
          z1 = 1w0;
-         transition start_0;
-     }
-     state start_0 {
          z = z1;
          transition accept;
      }
--- 2,8 ----
