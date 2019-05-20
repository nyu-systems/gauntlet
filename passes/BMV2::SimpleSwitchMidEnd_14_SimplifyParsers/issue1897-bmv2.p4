*** dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:01.410481900 +0200
--- dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:59:01.414328500 +0200
*************** parser ProtParser(packet_in packet, out
*** 29,37 ****
          addrType = hdr.addr_type.dstType;
          addr_1.ipv4.setInvalid();
          addr_1.ipv6.setInvalid();
-         transition ProtAddrParser_start;
-     }
-     state ProtAddrParser_start {
          transition select(addrType) {
              8w0x1: ProtAddrParser_ipv4;
              8w0x2: ProtAddrParser_ipv6;
--- 29,34 ----
*************** parser ProtParser(packet_in packet, out
*** 50,58 ****
          addrType = hdr.addr_type.srcType;
          addr_1.ipv4.setInvalid();
          addr_1.ipv6.setInvalid();
-         transition ProtAddrParser_start_0;
-     }
-     state ProtAddrParser_start_0 {
          transition select(addrType) {
              8w0x1: ProtAddrParser_ipv4_0;
              8w0x2: ProtAddrParser_ipv6_0;
--- 47,52 ----
