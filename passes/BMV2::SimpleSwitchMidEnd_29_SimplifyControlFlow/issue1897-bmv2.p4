--- dumps/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:16.961088800 +0200
+++ dumps/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:17.006293300 +0200
@@ -43,10 +43,8 @@ parser ProtParser(packet_in packet, out
         transition start_0;
     }
     state start_0 {
-        {
-            hdr.addr_dst.ipv4 = addr_1.ipv4;
-            hdr.addr_dst.ipv6 = addr_1.ipv6;
-        }
+        hdr.addr_dst.ipv4 = addr_1.ipv4;
+        hdr.addr_dst.ipv6 = addr_1.ipv6;
         addrType = hdr.addr_type.srcType;
         addr_1.ipv4.setInvalid();
         addr_1.ipv6.setInvalid();
@@ -64,10 +62,8 @@ parser ProtParser(packet_in packet, out
         transition start_1;
     }
     state start_1 {
-        {
-            hdr.addr_src.ipv4 = addr_1.ipv4;
-            hdr.addr_src.ipv6 = addr_1.ipv6;
-        }
+        hdr.addr_src.ipv4 = addr_1.ipv4;
+        hdr.addr_src.ipv6 = addr_1.ipv6;
         transition accept;
     }
 }
@@ -89,13 +85,11 @@ control ProtComputeChecksum(inout header
 }
 control ProtDeparser(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<addr_type_t>(hdr.addr_type);
-            packet.emit<addr_ipv4_t>(hdr.addr_dst.ipv4);
-            packet.emit<addr_ipv6_t>(hdr.addr_dst.ipv6);
-            packet.emit<addr_ipv4_t>(hdr.addr_src.ipv4);
-            packet.emit<addr_ipv6_t>(hdr.addr_src.ipv6);
-        }
+        packet.emit<addr_type_t>(hdr.addr_type);
+        packet.emit<addr_ipv4_t>(hdr.addr_dst.ipv4);
+        packet.emit<addr_ipv6_t>(hdr.addr_dst.ipv6);
+        packet.emit<addr_ipv4_t>(hdr.addr_src.ipv4);
+        packet.emit<addr_ipv6_t>(hdr.addr_src.ipv6);
     }
 }
 V1Switch<headers, metadata>(ProtParser(), ProtVerifyChecksum(), ProtIngress(), ProtEgress(), ProtComputeChecksum(), ProtDeparser()) main;
