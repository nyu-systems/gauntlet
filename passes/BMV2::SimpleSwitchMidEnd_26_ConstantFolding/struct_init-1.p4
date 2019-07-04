--- before_pass
+++ after_pass
@@ -11,13 +11,13 @@ control I(inout metadata_t meta) {
     H h_0;
     apply {
         h_0.setValid();
-        if (true && meta._foo__v0 == 9w192) {
+        if (meta._foo__v0 == 9w192) {
             meta._foo__v0 = meta._foo__v0 + 9w1;
             h_0.setValid();
             {
                 h_0.b = 32w2;
             }
-            if (!h_0.isValid() && !true || h_0.isValid() && true && h_0.b == 32w1) 
+            if (!h_0.isValid() && false || h_0.isValid() && true && h_0.b == 32w1) 
                 h_0.setValid();
         }
     }
