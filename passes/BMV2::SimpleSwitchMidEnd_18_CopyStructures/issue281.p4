*** dumps/p4_16_samples/issue281.p4/pruned/issue281-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:59:05.552854800 +0200
--- dumps/p4_16_samples/issue281.p4/pruned/issue281-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:05.556276500 +0200
*************** parser MyParser(packet_in b, out h hdr,
*** 46,53 ****
          l2_ether_0.setInvalid();
          b.extract<ethernet_t>(l2_ether_0);
          hdr_2.ether = l2_ether_0;
!         hdr = hdr_2;
!         hdr_3 = hdr;
          transition L3_start;
      }
      state L3_start {
--- 46,61 ----
          l2_ether_0.setInvalid();
          b.extract<ethernet_t>(l2_ether_0);
          hdr_2.ether = l2_ether_0;
!         {
!             hdr.ether = hdr_2.ether;
!             hdr.vlan = hdr_2.vlan;
!             hdr.ipv4 = hdr_2.ipv4;
!         }
!         {
!             hdr_3.ether = hdr.ether;
!             hdr_3.vlan = hdr.vlan;
!             hdr_3.ipv4 = hdr.ipv4;
!         }
          transition L3_start;
      }
      state L3_start {
*************** parser MyParser(packet_in b, out h hdr,
*** 71,77 ****
          transition L3_start;
      }
      state start_2 {
!         hdr = hdr_3;
          transition accept;
      }
  }
--- 79,89 ----
          transition L3_start;
      }
      state start_2 {
!         {
!             hdr.ether = hdr_3.ether;
!             hdr.vlan = hdr_3.vlan;
!             hdr.ipv4 = hdr_3.ipv4;
!         }
          transition accept;
      }
  }
