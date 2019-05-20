*** dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:09.803575900 +0200
--- dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:09.808738800 +0200
*************** control c(inout bit<32> b) {
*** 5,13 ****
      S s1;
      S s2;
      @name("c.a") action a_0() {
!         s2 = { 32w0 };
!         s1 = s2;
!         s2 = s1;
          b = s2.x;
      }
      apply {
--- 5,19 ----
      S s1;
      S s2;
      @name("c.a") action a_0() {
!         {
!             s2.x = 32w0;
!         }
!         {
!             s1.x = s2.x;
!         }
!         {
!             s2.x = s1.x;
!         }
          b = s2.x;
      }
      apply {
