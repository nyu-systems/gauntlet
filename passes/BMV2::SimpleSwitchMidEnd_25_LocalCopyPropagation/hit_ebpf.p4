--- dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:59.150333300 +0200
+++ dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:59.152852700 +0200
@@ -67,8 +67,6 @@ control pipe(inout Headers_t headers, ou
         }
         if (!hasReturned_0) {
             tmp_0 = Check_src_ip.apply().hit;
-            if (tmp_0) 
-                pass = pass;
         }
     }
 }
