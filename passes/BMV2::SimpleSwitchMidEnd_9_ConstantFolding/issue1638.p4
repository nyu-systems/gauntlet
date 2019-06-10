--- before_pass
+++ after_pass
@@ -29,7 +29,7 @@ control MyC(inout hdr_t hdr, inout meta_
     }
     apply {
         {
-            key_0 = meta_t {f0 = 8w0,f1 = 8w0,f2 = 8w0}.f0;
+            key_0 = 8w0;
             c2_a.apply();
         }
     }
