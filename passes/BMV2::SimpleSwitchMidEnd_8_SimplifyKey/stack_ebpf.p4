--- dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 17:32:11.867909700 +0200
+++ dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 17:32:11.870412800 +0200
@@ -46,9 +46,10 @@ control pipe(inout Headers_t headers, ou
         pass = false;
         headers.ipv4[0].srcAddr = add;
     }
+    bit<32> key_0;
     @name("pipe.Check_src_ip") table Check_src_ip {
         key = {
-            headers.ipv4[0].srcAddr: exact @name("headers.ipv4[0].srcAddr") ;
+            key_0: exact @name("headers.ipv4[0].srcAddr") ;
         }
         actions = {
             Reject_0();
@@ -59,11 +60,14 @@ control pipe(inout Headers_t headers, ou
     }
     apply {
         pass = true;
-        switch (Check_src_ip.apply().action_run) {
-            Reject_0: {
-                pass = false;
-            }
-            NoAction_0: {
+        {
+            key_0 = headers.ipv4[0].srcAddr;
+            switch (Check_src_ip.apply().action_run) {
+                Reject_0: {
+                    pass = false;
+                }
+                NoAction_0: {
+                }
             }
         }
     }
