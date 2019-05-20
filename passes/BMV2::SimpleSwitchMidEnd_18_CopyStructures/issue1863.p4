*** dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:59:00.150858100 +0200
--- dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:00.153263400 +0200
*************** struct S {
*** 5,12 ****
  control c(out bit<1> b) {
      S s;
      apply {
!         s = { 1w0, 1w1 };
!         s = { s.b, s.a };
          b = s.a;
      }
  }
--- 5,18 ----
  control c(out bit<1> b) {
      S s;
      apply {
!         {
!             s.a = 1w0;
!             s.b = 1w1;
!         }
!         {
!             s.a = s.b;
!             s.b = s.a;
!         }
          b = s.a;
      }
  }
