--- dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:20.484287400 +0200
+++ dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:20.486662700 +0200
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
