*** dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 17:00:53.281188200 +0200
--- dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 17:00:53.284058600 +0200
*************** parser p1(packet_in p, out Header h) {
*** 25,33 ****
          g(h.data2, tmp_6);
          h.data2 = h.data3 + 32w1;
          stack[1].isValid();
!         transition select(h.isValid()) {
!             true: next1;
!             false: next2;
          }
      }
      state next1 {
--- 25,33 ----
          g(h.data2, tmp_6);
          h.data2 = h.data3 + 32w1;
          stack[1].isValid();
!         transition select((bit<1>)h.isValid()) {
!             (bit<1>)true: next1;
!             (bit<1>)false: next2;
          }
      }
      state next1 {
