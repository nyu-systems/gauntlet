--- before_pass
+++ after_pass
@@ -25,10 +25,18 @@ control ComputeChecksumI(inout H hdr, in
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
     H hdr_1;
     apply {
-        hdr_1 = hdr;
-        hdr = hdr_1;
-        hdr_1 = hdr;
-        hdr = hdr_1;
+        {
+            hdr_1.stack = hdr.stack;
+        }
+        {
+            hdr.stack = hdr_1.stack;
+        }
+        {
+            hdr_1.stack = hdr.stack;
+        }
+        {
+            hdr.stack = hdr_1.stack;
+        }
     }
 }
 control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
