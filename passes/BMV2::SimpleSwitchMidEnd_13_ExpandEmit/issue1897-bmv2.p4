--- dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:30:35.303932800 +0200
+++ dumps/p4_16_samples/issue1897-bmv2.p4/pruned/issue1897-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:35.306526600 +0200
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
