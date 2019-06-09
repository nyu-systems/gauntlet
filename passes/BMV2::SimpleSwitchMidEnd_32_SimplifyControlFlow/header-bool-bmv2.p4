--- before_pass
+++ after_pass
@@ -50,10 +50,8 @@ control egress(inout Headers h, inout Me
 control deparser(packet_out b, in Headers h) {
     apply {
         b.emit<Hdr1>(h.h1);
-        {
-            b.emit<Hdr1>(h.u.h1);
-            b.emit<Hdr2>(h.u.h2);
-        }
+        b.emit<Hdr1>(h.u.h1);
+        b.emit<Hdr2>(h.u.h2);
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
