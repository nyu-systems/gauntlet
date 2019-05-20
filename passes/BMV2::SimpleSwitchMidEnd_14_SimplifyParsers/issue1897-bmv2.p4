--- dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:35.306526600 +0200
+++ dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:30:35.308982300 +0200
@@ -29,9 +29,6 @@ parser ProtParser(packet_in packet, out
         addrType = hdr.addr_type.dstType;
         addr_1.ipv4.setInvalid();
         addr_1.ipv6.setInvalid();
-        transition ProtAddrParser_start;
-    }
-    state ProtAddrParser_start {
         transition select(addrType) {
             8w0x1: ProtAddrParser_ipv4;
             8w0x2: ProtAddrParser_ipv6;
@@ -50,9 +47,6 @@ parser ProtParser(packet_in packet, out
         addrType = hdr.addr_type.srcType;
         addr_1.ipv4.setInvalid();
         addr_1.ipv6.setInvalid();
-        transition ProtAddrParser_start_0;
-    }
-    state ProtAddrParser_start_0 {
         transition select(addrType) {
             8w0x1: ProtAddrParser_ipv4_0;
             8w0x2: ProtAddrParser_ipv6_0;
