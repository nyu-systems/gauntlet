--- before_pass
+++ after_pass
@@ -54,7 +54,12 @@ control uc(inout headers hdr, inout meta
 }
 control deparser(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>(hdr);
+        {
+            packet.emit<H>(hdr.h);
+            packet.emit<H>(hdr.a[0]);
+            packet.emit<H>(hdr.a[1]);
+            packet.emit<Same>(hdr.same);
+        }
     }
 }
 V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
