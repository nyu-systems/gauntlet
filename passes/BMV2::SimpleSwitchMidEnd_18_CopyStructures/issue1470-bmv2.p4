*** dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:46.659319200 +0200
--- dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:46.661489000 +0200
*************** parser OuterParser(packet_in pkt, out he
*** 41,47 ****
          transition start_0;
      }
      state start_0 {
!         hdr = hdr_1;
          transition accept;
      }
  }
--- 41,50 ----
          transition start_0;
      }
      state start_0 {
!         {
!             hdr.eth = hdr_1.eth;
!             hdr.ipv4 = hdr_1.ipv4;
!         }
          transition accept;
      }
  }
