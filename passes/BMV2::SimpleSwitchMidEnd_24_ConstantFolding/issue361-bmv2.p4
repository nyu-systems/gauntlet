*** dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:09.465240300 +0200
--- dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:09.467532500 +0200
*************** parser MyParser(packet_in b, out my_pack
*** 13,20 ****
      state start {
          bv = true;
          transition select((bit<1>)bv) {
!             (bit<1>)false: next;
!             (bit<1>)true: accept;
          }
      }
      state next {
--- 13,20 ----
      state start {
          bv = true;
          transition select((bit<1>)bv) {
!             1w0: next;
!             1w1: accept;
          }
      }
      state next {
