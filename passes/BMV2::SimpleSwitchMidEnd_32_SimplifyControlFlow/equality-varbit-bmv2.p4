--- before_pass
+++ after_pass
@@ -38,9 +38,7 @@ control uc(inout headers hdr, inout meta
 }
 control deparser(packet_out packet, in headers hdr) {
     apply {
-        {
-            packet.emit<H>(hdr.h);
-        }
+        packet.emit<H>(hdr.h);
     }
 }
 V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
