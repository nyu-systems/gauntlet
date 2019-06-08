--- before_pass
+++ after_pass
@@ -28,9 +28,7 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        {
-            b.emit<hdr>(h.h);
-        }
+        b.emit<hdr>(h.h);
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
