*** dumps/p4_16_samples/nested_select.p4/pruned/nested_select-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:59:49.515094000 +0200
--- dumps/p4_16_samples/nested_select.p4/pruned/nested_select-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 16:59:49.517287900 +0200
*************** parser p() {
*** 3,11 ****
      bit<8> x;
      state start {
          x = 8w5;
!         transition select(x, x, { x, x }, x) {
!             (8w0, 8w0, { 8w0, 8w0 }, 8w0): accept;
!             (8w1, 8w1, default, 8w1): accept;
              default: reject;
          }
      }
--- 3,11 ----
      bit<8> x;
      state start {
          x = 8w5;
!         transition select(x, x, x, x, x) {
!             (8w0, 8w0, 8w0, 8w0, 8w0): accept;
!             (8w1, 8w1, default, default, 8w1): accept;
              default: reject;
          }
      }
