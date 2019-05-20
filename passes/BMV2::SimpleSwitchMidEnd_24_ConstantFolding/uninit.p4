*** dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:00:53.288648100 +0200
--- dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:53.290967800 +0200
*************** parser p1(packet_in p, out Header h) {
*** 26,33 ****
          h.data2 = h.data3 + 32w1;
          stack[1].isValid();
          transition select((bit<1>)h.isValid()) {
!             (bit<1>)true: next1;
!             (bit<1>)false: next2;
          }
      }
      state next1 {
--- 26,33 ----
          h.data2 = h.data3 + 32w1;
          stack[1].isValid();
          transition select((bit<1>)h.isValid()) {
!             1w1: next1;
!             1w0: next2;
          }
      }
      state next1 {
