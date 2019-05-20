*** dumps/p4_16_samples/parser-conditional.p4/pruned/parser-conditional-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 16:59:53.742364200 +0200
--- dumps/p4_16_samples/parser-conditional.p4/pruned/parser-conditional-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:59:53.745047500 +0200
*************** parser p(out bit<32> b) {
*** 6,14 ****
      bit<32> tmp_4;
      state start {
          a = 32w1;
!         transition select(a == 32w0) {
!             true: start_true;
!             false: start_false;
          }
      }
      state start_true {
--- 6,14 ----
      bit<32> tmp_4;
      state start {
          a = 32w1;
!         transition select((bit<1>)(a == 32w0)) {
!             (bit<1>)true: start_true;
!             (bit<1>)false: start_false;
          }
      }
      state start_true {
*************** parser p(out bit<32> b) {
*** 22,36 ****
      state start_join {
          b = tmp_2;
          b = b + 32w1;
!         transition select(a > 32w0) {
!             true: start_true_0;
!             false: start_false_0;
          }
      }
      state start_true_0 {
!         transition select(a > 32w1) {
!             true: start_true_0_true;
!             false: start_true_0_false;
          }
      }
      state start_true_0_true {
--- 22,36 ----
      state start_join {
          b = tmp_2;
          b = b + 32w1;
!         transition select((bit<1>)(a > 32w0)) {
!             (bit<1>)true: start_true_0;
!             (bit<1>)false: start_false_0;
          }
      }
      state start_true_0 {
!         transition select((bit<1>)(a > 32w1)) {
!             (bit<1>)true: start_true_0_true;
!             (bit<1>)false: start_true_0_false;
          }
      }
      state start_true_0_true {
