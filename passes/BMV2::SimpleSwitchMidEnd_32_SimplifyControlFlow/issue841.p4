--- before_pass
+++ after_pass
@@ -38,11 +38,9 @@ control MyComputeChecksum(inout headers
     @name("MyComputeChecksum.checksum") Checksum16() checksum_0;
     apply {
         h_0.setValid();
-        {
-            h_0.src = hdr.h.src;
-            h_0.dst = hdr.h.dst;
-            h_0.csum = 16w0;
-        }
+        h_0.src = hdr.h.src;
+        h_0.dst = hdr.h.dst;
+        h_0.csum = 16w0;
         tmp = checksum_0.get<h_t>(h_0);
         hdr.h.csum = tmp;
     }
