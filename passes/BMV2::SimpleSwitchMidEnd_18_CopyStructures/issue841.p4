--- before_pass
+++ after_pass
@@ -38,7 +38,11 @@ control MyComputeChecksum(inout headers
     @name("MyComputeChecksum.checksum") Checksum16() checksum;
     apply {
         h_1.setValid();
-        h_1 = { hdr.h.src, hdr.h.dst, 16w0 };
+        {
+            h_1.src = hdr.h.src;
+            h_1.dst = hdr.h.dst;
+            h_1.csum = 16w0;
+        }
         tmp_0 = checksum.get<h_t>(h_1);
         hdr.h.csum = tmp_0;
     }
