--- before_pass
+++ after_pass
@@ -44,7 +44,10 @@ control egress(inout Headers h, inout Me
 control deparser(packet_out b, in Headers h) {
     apply {
         b.emit<Hdr1>(h.h1);
-        b.emit<U>(h.u);
+        {
+            b.emit<Hdr1>(h.u.h1);
+            b.emit<Hdr2>(h.u.h2);
+        }
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
