--- before_pass
+++ after_pass
@@ -66,10 +66,8 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<S>(hdr.base);
-            packet.emit<U>(hdr.u[0]);
-        }
+        packet.emit<S>(hdr.base);
+        packet.emit<U>(hdr.u[0]);
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
