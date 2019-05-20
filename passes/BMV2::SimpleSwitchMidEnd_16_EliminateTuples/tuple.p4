*** dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:00:50.924450100 +0200
--- dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:00:50.931886200 +0200
*************** struct S {
*** 4,11 ****
  }
  control proto();
  package top(proto _p);
  control c() {
!     tuple<bit<32>, bool> x;
      apply {
          x = { 32w10, false };
      }
--- 4,15 ----
  }
  control proto();
  package top(proto _p);
+ struct tuple_0 {
+     bit<32> field;
+     bool    field_0;
+ }
  control c() {
!     tuple_0 x;
      apply {
          x = { 32w10, false };
      }
