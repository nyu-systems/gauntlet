*** dumps/p4_16_samples/issue281.p4/pruned/issue281-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:05.585930700 +0200
--- dumps/p4_16_samples/issue281.p4/pruned/issue281-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:05.645549000 +0200
*************** parser MyParser(packet_in b, out h hdr,
*** 50,65 ****
          l2_ether_0.setInvalid();
          b.extract<ethernet_t>(l2_ether_0);
          hdr_2_ether = l2_ether_0;
!         {
!             hdr.ether = hdr_2_ether;
!             hdr.vlan = hdr_2_vlan;
!             hdr.ipv4 = hdr_2_ipv4;
!         }
!         {
!             hdr_3_ether = hdr.ether;
!             hdr_3_vlan = hdr.vlan;
!             hdr_3_ipv4 = hdr.ipv4;
!         }
          transition L3_start;
      }
      state L3_start {
--- 50,61 ----
          l2_ether_0.setInvalid();
          b.extract<ethernet_t>(l2_ether_0);
          hdr_2_ether = l2_ether_0;
!         hdr.ether = hdr_2_ether;
!         hdr.vlan = hdr_2_vlan;
!         hdr.ipv4 = hdr_2_ipv4;
!         hdr_3_ether = hdr.ether;
!         hdr_3_vlan = hdr.vlan;
!         hdr_3_ipv4 = hdr.ipv4;
          transition L3_start;
      }
      state L3_start {
*************** parser MyParser(packet_in b, out h hdr,
*** 83,93 ****
          transition L3_start;
      }
      state start_2 {
!         {
!             hdr.ether = hdr_3_ether;
!             hdr.vlan = hdr_3_vlan;
!             hdr.ipv4 = hdr_3_ipv4;
!         }
          transition accept;
      }
  }
--- 79,87 ----
          transition L3_start;
      }
      state start_2 {
!         hdr.ether = hdr_3_ether;
!         hdr.vlan = hdr_3_vlan;
!         hdr.ipv4 = hdr_3_ipv4;
          transition accept;
      }
  }
