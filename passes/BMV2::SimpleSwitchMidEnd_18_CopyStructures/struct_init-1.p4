--- before_pass
+++ after_pass
@@ -14,7 +14,9 @@ control I(inout metadata_t meta) {
         if (true && meta.foo._v == 9w192) {
             meta.foo._v = meta.foo._v + 9w1;
             h_0.setValid();
-            h_0 = H {b = 32w2};
+            {
+                h_0.b = 32w2;
+            }
             if (!h_0.isValid() && !true || h_0.isValid() && true && h_0.b == 32w1) 
                 h_0.setValid();
         }
