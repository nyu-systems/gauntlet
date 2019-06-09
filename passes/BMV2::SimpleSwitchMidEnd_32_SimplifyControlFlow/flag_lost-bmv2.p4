--- before_pass
+++ after_pass
@@ -88,10 +88,8 @@ control computeChecksum(inout headers hd
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<ethernet_t>(hdr.ethernet);
-            packet.emit<ipv4_t>(hdr.ipv4);
-        }
+        packet.emit<ethernet_t>(hdr.ethernet);
+        packet.emit<ipv4_t>(hdr.ipv4);
     }
 }
 V1Switch<headers, metadata>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
