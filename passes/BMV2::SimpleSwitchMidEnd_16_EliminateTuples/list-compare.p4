*** dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:00:38.326749100 +0200
--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:00:38.330010800 +0200
*************** struct S {
*** 4,11 ****
  }
  control c(out bool z);
  package top(c _c);
  control test(out bool zout) {
!     tuple<bit<32>, bit<32>> p;
      S q;
      apply {
          p = { 32w4, 32w5 };
--- 4,15 ----
  }
  control c(out bool z);
  package top(c _c);
+ struct tuple_0 {
+     bit<32> field;
+     bit<32> field_0;
+ }
  control test(out bool zout) {
!     tuple_0 p;
      S q;
      apply {
          p = { 32w4, 32w5 };
