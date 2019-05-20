*** dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 16:59:09.454462900 +0200
--- dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:59:09.458686500 +0200
*************** parser MyParser(packet_in b, out my_pack
*** 12,20 ****
      bool bv;
      state start {
          bv = true;
!         transition select(bv) {
!             false: next;
!             true: accept;
          }
      }
      state next {
--- 12,20 ----
      bool bv;
      state start {
          bv = true;
!         transition select((bit<1>)bv) {
!             (bit<1>)false: next;
!             (bit<1>)true: accept;
          }
      }
      state next {
