*** dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 16:58:11.673921800 +0200
--- dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:58:11.676700500 +0200
*************** parser p0(packet_in p, out Header h) {
*** 7,21 ****
      state start {
          b = true;
          p.extract<Header>(h);
!         transition select(h.data, b) {
!             (default, true): next;
              (default, default): reject;
          }
      }
      state next {
          p.extract<Header>(h);
!         transition select(h.data, b) {
!             (default, true): accept;
              (default, default): reject;
              default: reject;
          }
--- 7,21 ----
      state start {
          b = true;
          p.extract<Header>(h);
!         transition select(h.data, (bit<1>)b) {
!             (default, (bit<1>)true): next;
              (default, default): reject;
          }
      }
      state next {
          p.extract<Header>(h);
!         transition select(h.data, (bit<1>)b) {
!             (default, (bit<1>)true): accept;
              (default, default): reject;
              default: reject;
          }
