*** dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:29.138267700 +0200
--- dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:59:29.141191800 +0200
*************** parser MyP1(packet_in pkt, out headers_t
*** 12,20 ****
      headers_t hdr_1;
      state start {
          hdr_1.data.setInvalid();
-         transition MyP2_start;
-     }
-     state MyP2_start {
          transition reject;
      }
  }
--- 12,17 ----
