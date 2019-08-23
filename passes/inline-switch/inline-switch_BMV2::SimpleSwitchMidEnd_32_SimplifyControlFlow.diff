--- before_pass
+++ after_pass
@@ -11,13 +11,11 @@ control d(out bit<32> x) {
         default_action = cinst_a1_0();
     }
     apply {
-        {
-            switch (cinst_t.apply().action_run) {
-                cinst_a1_0: 
-                cinst_a2_0: {
-                }
-                default: {
-                }
+        switch (cinst_t.apply().action_run) {
+            cinst_a1_0: 
+            cinst_a2_0: {
+            }
+            default: {
             }
         }
     }
