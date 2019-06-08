--- dumps/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_30_CompileTimeOperations.p4	2019-06-08 18:31:48.041037900 +0200
+++ dumps/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:31:48.043398700 +0200
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
