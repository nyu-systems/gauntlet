--- before_pass
+++ after_pass
@@ -65,7 +65,10 @@ control egress(inout headers hdr, inout
 }
 control DeparserImpl(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<S>(hdr.base);
+            packet.emit<U>(hdr.u[0]);
+        }
     }
 }
 control verifyChecksum(inout headers hdr, inout metadata meta) {
