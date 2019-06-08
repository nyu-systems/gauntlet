--- before_pass
+++ after_pass
@@ -5,8 +5,6 @@ struct headers {
 }
 control MyDeparser(packet_out packet, in headers hdr) {
     apply {
-        {
-        }
     }
 }
 Switch<headers>(MyDeparser()) main;
