--- before_pass
+++ after_pass
@@ -11,13 +11,11 @@ control d(out bit<32> x) {
         default_action = cinst_a1();
     }
     apply {
-        {
-            switch (cinst_t_0.apply().action_run) {
-                cinst_a1: 
-                cinst_a2: {
-                }
-                default: {
-                }
+        switch (cinst_t_0.apply().action_run) {
+            cinst_a1: 
+            cinst_a2: {
+            }
+            default: {
             }
         }
     }
