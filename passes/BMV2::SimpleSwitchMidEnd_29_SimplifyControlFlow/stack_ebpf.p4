--- dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:11.818888700 +0200
+++ dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:11.821305300 +0200
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
