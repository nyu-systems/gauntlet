--- before_pass
+++ after_pass
@@ -89,7 +89,13 @@ control ProtComputeChecksum(inout header
 }
 control ProtDeparser(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<addr_type_t>(hdr.addr_type);
+            packet.emit<addr_ipv4_t>(hdr.addr_dst.ipv4);
+            packet.emit<addr_ipv6_t>(hdr.addr_dst.ipv6);
+            packet.emit<addr_ipv4_t>(hdr.addr_src.ipv4);
+            packet.emit<addr_ipv6_t>(hdr.addr_src.ipv6);
+        }
     }
 }
 V1Switch<headers, metadata>(ProtParser(), ProtVerifyChecksum(), ProtIngress(), ProtEgress(), ProtComputeChecksum(), ProtDeparser()) main;
