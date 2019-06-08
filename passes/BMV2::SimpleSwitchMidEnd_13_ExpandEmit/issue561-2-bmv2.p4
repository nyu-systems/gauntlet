--- before_pass
+++ after_pass
@@ -69,7 +69,11 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<S>(hdr.base);
+            packet.emit<O1>(hdr.u.byte);
+            packet.emit<O2>(hdr.u.short);
+        }
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
