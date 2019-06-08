--- before_pass
+++ after_pass
@@ -23,19 +23,19 @@ control ComputeChecksumI(inout H hdr, in
     }
 }
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
-    H hdr_1;
+    h_t[1] hdr_1_stack;
     apply {
         {
-            hdr_1.stack = hdr.stack;
+            hdr_1_stack = hdr.stack;
         }
         {
-            hdr.stack = hdr_1.stack;
+            hdr.stack = hdr_1_stack;
         }
         {
-            hdr_1.stack = hdr.stack;
+            hdr_1_stack = hdr.stack;
         }
         {
-            hdr.stack = hdr_1.stack;
+            hdr.stack = hdr_1_stack;
         }
     }
 }
