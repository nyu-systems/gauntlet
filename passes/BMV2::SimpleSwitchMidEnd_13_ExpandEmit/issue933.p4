--- before_pass
+++ after_pass
@@ -5,7 +5,8 @@ struct headers {
 }
 control MyDeparser(packet_out packet, in headers hdr) {
     apply {
-        packet.emit<headers>({});
+        {
+        }
     }
 }
 Switch<headers>(MyDeparser()) main;
