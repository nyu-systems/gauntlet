--- before_pass
+++ after_pass
@@ -35,7 +35,11 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<hdr[3]>(h.hs);
+        {
+            b.emit<hdr>(h.hs[0]);
+            b.emit<hdr>(h.hs[1]);
+            b.emit<hdr>(h.hs[2]);
+        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
