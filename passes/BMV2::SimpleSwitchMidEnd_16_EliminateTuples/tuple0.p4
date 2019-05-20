*** dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:00:51.230822600 +0200
--- dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:00:51.235556700 +0200
***************
*** 1,8 ****
! extern void f(in tuple<bit<32>, bool> data);
  control proto();
  package top(proto _p);
  control c() {
!     tuple<bit<32>, bool> x;
      apply {
          x = { 32w10, false };
          f(x);
--- 1,12 ----
! struct tuple_0 {
!     bit<32> field;
!     bool    field_0;
! }
! extern void f(in tuple_0 data);
  control proto();
  package top(proto _p);
  control c() {
!     tuple_0 x;
      apply {
          x = { 32w10, false };
          f(x);
