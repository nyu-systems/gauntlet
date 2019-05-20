--- dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_30_CompileTimeOperations.p4	2019-05-20 17:29:59.164555800 +0200
+++ dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:29:59.166598800 +0200
@@ -66,7 +66,10 @@ control pipe(inout Headers_t headers, ou
             hasReturned_0 = true;
         }
         if (!hasReturned_0) 
-            tmp_0 = Check_src_ip.apply().hit;
+            if (Check_src_ip.apply().hit) 
+                tmp_0 = true;
+            else 
+                tmp_0 = false;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
