*** dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:09.826986600 +0200
--- dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:09.831893900 +0200
*************** struct S {
*** 2,20 ****
      bit<32> x;
  }
  control c(inout bit<32> b) {
-     S s1;
-     S s2;
      @name("c.a") action a_0() {
          {
-             s2.x = 32w0;
          }
          {
-             s1.x = s2.x;
          }
          {
-             s2.x = s1.x;
          }
!         b = s2.x;
      }
      apply {
          a_0();
--- 2,15 ----
      bit<32> x;
  }
  control c(inout bit<32> b) {
      @name("c.a") action a_0() {
          {
          }
          {
          }
          {
          }
!         b = 32w0;
      }
      apply {
          a_0();
