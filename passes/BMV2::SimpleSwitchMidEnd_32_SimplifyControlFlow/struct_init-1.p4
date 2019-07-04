--- before_pass
+++ after_pass
@@ -14,9 +14,7 @@ control I(inout metadata_t meta) {
         if (meta._foo__v0 == 9w192) {
             meta._foo__v0 = meta._foo__v0 + 9w1;
             h_0.setValid();
-            {
-                h_0.b = 32w2;
-            }
+            h_0.b = 32w2;
             if (!h_0.isValid() && false || h_0.isValid() && true && false) 
                 h_0.setValid();
         }
