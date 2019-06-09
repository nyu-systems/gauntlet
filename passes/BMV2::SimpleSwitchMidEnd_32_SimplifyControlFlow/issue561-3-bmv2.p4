--- before_pass
+++ after_pass
@@ -75,11 +75,9 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<S>(hdr.base);
-            packet.emit<O1>(hdr.u.byte);
-            packet.emit<O2>(hdr.u.short);
-        }
+        packet.emit<S>(hdr.base);
+        packet.emit<O1>(hdr.u.byte);
+        packet.emit<O2>(hdr.u.short);
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
