--- dumps/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:02.806236800 +0200
+++ dumps/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:02.809966300 +0200
@@ -59,13 +59,11 @@ control pipe(inout Headers_t headers, ou
     }
     apply {
         pass = true;
-        {
-            switch (Check_src_ip.apply().action_run) {
-                Reject_0: {
-                    pass = false;
-                }
-                NoAction_0: {
-                }
+        switch (Check_src_ip.apply().action_run) {
+            Reject_0: {
+                pass = false;
+            }
+            NoAction_0: {
             }
         }
     }
