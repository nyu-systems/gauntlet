--- before_pass
+++ after_pass
@@ -34,9 +34,7 @@ control cc(inout Headers hdr, inout M me
 }
 control d(packet_out b, in Headers hdr) {
     apply {
-        {
-            b.emit<Header>(hdr.h);
-        }
+        b.emit<Header>(hdr.h);
     }
 }
 V1Switch<Headers, M>(prs(), vc(), i(), e(), cc(), d()) main;
