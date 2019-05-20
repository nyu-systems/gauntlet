*** dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 16:59:49.211561300 +0200
--- dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:59:49.215558700 +0200
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
  extern void f<D>(in D data);
  control c(inout bit<1> r) {
--- 1,14 ----
  struct T {
      bit<1> f;
  }
+ struct tuple_0 {
+     T field;
+     T field_0;
+ }
  struct S {
!     tuple_0 f1;
!     T       f2;
!     bit<1>  z;
  }
  extern void f<D>(in D data);
  control c(inout bit<1> r) {
*************** control c(inout bit<1> r) {
*** 12,18 ****
      bit<1> tmp;
      apply {
          s_0 = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
!         f<tuple<T, T>>(s_0.f1);
          tmp = s_0.f2.f & s_0.z;
          r = tmp;
      }
--- 16,22 ----
      bit<1> tmp;
      apply {
          s_0 = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
!         f<tuple_0>(s_0.f1);
          tmp = s_0.f2.f & s_0.z;
          r = tmp;
      }
