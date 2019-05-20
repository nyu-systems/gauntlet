*** dumps/p4_16_samples/nested-tuple.p4/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:59:48.923881900 +0200
--- dumps/p4_16_samples/nested-tuple.p4/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:48.929748200 +0200
*************** extern void f<T>(in T data);
*** 18,24 ****
  control c(inout bit<1> r) {
      S s;
      apply {
!         s = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
          f<tuple_1>(s.f1);
          f<tuple_0>({ { 1w0 }, { 1w1 } });
          r = s.f2.f & s.z;
--- 18,37 ----
  control c(inout bit<1> r) {
      S s;
      apply {
!         {
!             {
!                 {
!                     s.f1.field_1.f = 1w0;
!                 }
!                 {
!                     s.f1.field_2.f = 1w1;
!                 }
!             }
!             {
!                 s.f2.f = 1w0;
!             }
!             s.z = 1w1;
!         }
          f<tuple_1>(s.f1);
          f<tuple_0>({ { 1w0 }, { 1w1 } });
          r = s.f2.f & s.z;
