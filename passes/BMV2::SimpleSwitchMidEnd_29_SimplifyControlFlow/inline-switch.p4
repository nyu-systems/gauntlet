--- dumps/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:51.075211500 +0200
+++ dumps/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:51.113249700 +0200
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
