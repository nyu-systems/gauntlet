--- before_pass
+++ after_pass
@@ -105,7 +105,13 @@ control uc(inout headers hdr, inout meta
 control DeparserI(packet_out packet, in headers hdr) {
     apply {
         packet.emit<h1_t>(hdr.h1);
-        packet.emit<h2_t[5]>(hdr.h2);
+        {
+            packet.emit<h2_t>(hdr.h2[0]);
+            packet.emit<h2_t>(hdr.h2[1]);
+            packet.emit<h2_t>(hdr.h2[2]);
+            packet.emit<h2_t>(hdr.h2[3]);
+            packet.emit<h2_t>(hdr.h2[4]);
+        }
         packet.emit<h3_t>(hdr.h3);
     }
 }
