--- dumps/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:48.036832700 +0200
+++ dumps/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:48.082741200 +0200
@@ -65,9 +65,8 @@ control pipe(inout Headers_t headers, ou
             pass = false;
             hasReturned_0 = true;
         }
-        if (!hasReturned_0) {
+        if (!hasReturned_0) 
             tmp_0 = Check_src_ip.apply().hit;
-        }
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
