*** dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:01.462356400 +0200
--- dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:01.522296800 +0200
*************** parser ProtParser(packet_in packet, out
*** 43,52 ****
          transition start_0;
      }
      state start_0 {
!         {
!             hdr.addr_dst.ipv4 = addr_1.ipv4;
!             hdr.addr_dst.ipv6 = addr_1.ipv6;
!         }
          addrType = hdr.addr_type.srcType;
          addr_1.ipv4.setInvalid();
          addr_1.ipv6.setInvalid();
--- 43,50 ----
          transition start_0;
      }
      state start_0 {
!         hdr.addr_dst.ipv4 = addr_1.ipv4;
!         hdr.addr_dst.ipv6 = addr_1.ipv6;
          addrType = hdr.addr_type.srcType;
          addr_1.ipv4.setInvalid();
          addr_1.ipv6.setInvalid();
*************** parser ProtParser(packet_in packet, out
*** 64,73 ****
          transition start_1;
      }
      state start_1 {
!         {
!             hdr.addr_src.ipv4 = addr_1.ipv4;
!             hdr.addr_src.ipv6 = addr_1.ipv6;
!         }
          transition accept;
      }
  }
--- 62,69 ----
          transition start_1;
      }
      state start_1 {
!         hdr.addr_src.ipv4 = addr_1.ipv4;
!         hdr.addr_src.ipv6 = addr_1.ipv6;
          transition accept;
      }
  }
*************** control ProtComputeChecksum(inout header
*** 89,101 ****
  }
  control ProtDeparser(packet_out packet, in headers hdr) {
      apply {
!         {
!             packet.emit<addr_type_t>(hdr.addr_type);
!             packet.emit<addr_ipv4_t>(hdr.addr_dst.ipv4);
!             packet.emit<addr_ipv6_t>(hdr.addr_dst.ipv6);
!             packet.emit<addr_ipv4_t>(hdr.addr_src.ipv4);
!             packet.emit<addr_ipv6_t>(hdr.addr_src.ipv6);
!         }
      }
  }
  V1Switch<headers, metadata>(ProtParser(), ProtVerifyChecksum(), ProtIngress(), ProtEgress(), ProtComputeChecksum(), ProtDeparser()) main;
--- 85,95 ----
  }
  control ProtDeparser(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<addr_type_t>(hdr.addr_type);
!         packet.emit<addr_ipv4_t>(hdr.addr_dst.ipv4);
!         packet.emit<addr_ipv6_t>(hdr.addr_dst.ipv6);
!         packet.emit<addr_ipv4_t>(hdr.addr_src.ipv4);
!         packet.emit<addr_ipv6_t>(hdr.addr_src.ipv6);
      }
  }
  V1Switch<headers, metadata>(ProtParser(), ProtVerifyChecksum(), ProtIngress(), ProtEgress(), ProtComputeChecksum(), ProtDeparser()) main;
