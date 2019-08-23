--- before_pass
+++ after_pass
@@ -29,9 +29,6 @@ parser ProtParser(packet_in packet, out
         addrType_0 = hdr.addr_type.dstType;
         addr_0.ipv4.setInvalid();
         addr_0.ipv6.setInvalid();
-        transition ProtAddrParser_start;
-    }
-    state ProtAddrParser_start {
         transition select(addrType_0) {
             8w0x1: ProtAddrParser_ipv4;
             8w0x2: ProtAddrParser_ipv6;
@@ -50,9 +47,6 @@ parser ProtParser(packet_in packet, out
         addrType_0 = hdr.addr_type.srcType;
         addr_0.ipv4.setInvalid();
         addr_0.ipv6.setInvalid();
-        transition ProtAddrParser_start_0;
-    }
-    state ProtAddrParser_start_0 {
         transition select(addrType_0) {
             8w0x1: ProtAddrParser_ipv4_0;
             8w0x2: ProtAddrParser_ipv6_0;
