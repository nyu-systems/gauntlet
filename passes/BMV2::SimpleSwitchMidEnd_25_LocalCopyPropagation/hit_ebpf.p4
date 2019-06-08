--- dumps/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:48.027105500 +0200
+++ dumps/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:48.030047500 +0200
@@ -67,8 +67,6 @@ control pipe(inout Headers_t headers, ou
         }
         if (!hasReturned_0) {
             tmp_0 = Check_src_ip.apply().hit;
-            if (tmp_0) 
-                pass = pass;
         }
     }
 }
