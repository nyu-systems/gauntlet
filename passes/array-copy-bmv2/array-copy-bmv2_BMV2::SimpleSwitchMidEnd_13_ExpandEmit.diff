--- before_pass
+++ after_pass
@@ -31,7 +31,12 @@ control egress(inout Headers h, inout Me
 }
 control deparser(packet_out b, in Headers h) {
     apply {
-        b.emit<Headers>(h);
+        {
+            b.emit<Hdr>(h.h1[0]);
+            b.emit<Hdr>(h.h1[1]);
+            b.emit<Hdr>(h.h2[0]);
+            b.emit<Hdr>(h.h2[1]);
+        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
