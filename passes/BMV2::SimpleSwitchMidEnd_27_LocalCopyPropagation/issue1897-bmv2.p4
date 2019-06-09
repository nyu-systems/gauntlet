--- before_pass
+++ after_pass
@@ -22,14 +22,12 @@ struct headers {
     addr_t      addr_src;
 }
 parser ProtParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<8> addrType_0;
     addr_t addr_0;
     state start {
         packet.extract<addr_type_t>(hdr.addr_type);
-        addrType_0 = hdr.addr_type.dstType;
         addr_0.ipv4.setInvalid();
         addr_0.ipv6.setInvalid();
-        transition select(addrType_0) {
+        transition select(hdr.addr_type.dstType) {
             8w0x1: ProtAddrParser_ipv4;
             8w0x2: ProtAddrParser_ipv6;
         }
@@ -47,10 +45,9 @@ parser ProtParser(packet_in packet, out
             hdr.addr_dst.ipv4 = addr_0.ipv4;
             hdr.addr_dst.ipv6 = addr_0.ipv6;
         }
-        addrType_0 = hdr.addr_type.srcType;
         addr_0.ipv4.setInvalid();
         addr_0.ipv6.setInvalid();
-        transition select(addrType_0) {
+        transition select(hdr.addr_type.srcType) {
             8w0x1: ProtAddrParser_ipv4_0;
             8w0x2: ProtAddrParser_ipv6_0;
         }
