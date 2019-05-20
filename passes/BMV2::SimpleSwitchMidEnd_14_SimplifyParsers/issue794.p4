*** dumps/p4_16_samples/issue794.p4/pruned/issue794-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:57:44.437401500 +0200
--- dumps/p4_16_samples/issue794.p4/pruned/issue794-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:57:44.439635100 +0200
*************** extern Random2 {
*** 9,21 ****
  parser caller() {
      @name("caller.rand1") Random2() rand1;
      state start {
-         transition callee_start;
-     }
-     state callee_start {
          rand1.read();
-         transition start_0;
-     }
-     state start_0 {
          transition accept;
      }
  }
--- 9,15 ----
