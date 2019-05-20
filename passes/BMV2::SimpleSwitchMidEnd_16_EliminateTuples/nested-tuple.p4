*** dumps/p4_16_samples/nested-tuple.p4/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 16:59:48.916270400 +0200
--- dumps/p4_16_samples/nested-tuple.p4/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:59:48.919056000 +0200
***************
*** 1,10 ****
  struct T {
      bit<1> f;
  }
  struct S {
!     tuple<T, T> f1;
!     T           f2;
!     bit<1>      z;
  }
  struct tuple_0 {
      T field;
--- 1,14 ----
  struct T {
      bit<1> f;
  }
+ struct tuple_1 {
+     T field_1;
+     T field_2;
+ }
  struct S {
!     tuple_1 f1;
!     T       f2;
!     bit<1>  z;
  }
  struct tuple_0 {
      T field;
*************** control c(inout bit<1> r) {
*** 15,21 ****
      S s;
      apply {
          s = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
!         f<tuple<T, T>>(s.f1);
          f<tuple_0>({ { 1w0 }, { 1w1 } });
          r = s.f2.f & s.z;
      }
--- 19,25 ----
      S s;
      apply {
          s = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
!         f<tuple_1>(s.f1);
          f<tuple_0>({ { 1w0 }, { 1w1 } });
          r = s.f2.f & s.z;
      }
