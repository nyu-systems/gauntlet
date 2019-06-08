--- dumps/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:53.973277100 +0200
+++ dumps/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:53.976373200 +0200
@@ -64,11 +64,9 @@ control pipe(inout Headers_t headers, ou
         default_action = drop_0();
     }
     apply {
-        {
-            key_0 = headers.ipv4.srcAddr + 32w1;
-            key_1 = headers.ipv4.dstAddr + 32w1;
-            t.apply();
-        }
+        key_0 = headers.ipv4.srcAddr + 32w1;
+        key_1 = headers.ipv4.dstAddr + 32w1;
+        t.apply();
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
