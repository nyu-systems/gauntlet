*** dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:00.176927300 +0200
--- dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:00.180303500 +0200
*************** struct S {
*** 3,19 ****
      bit<1> b;
  }
  control c(out bit<1> b) {
-     S s;
      apply {
          {
-             s.a = 1w0;
-             s.b = 1w1;
          }
          {
-             s.a = s.b;
-             s.b = s.a;
          }
!         b = s.a;
      }
  }
  control e<T>(out T t);
--- 3,14 ----
      bit<1> b;
  }
  control c(out bit<1> b) {
      apply {
          {
          }
          {
          }
!         b = 1w1;
      }
  }
  control e<T>(out T t);
