--- dumps/p4_16_samples/two_ebpf.p4/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:32.780238800 +0200
+++ dumps/p4_16_samples/two_ebpf.p4/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:32.782760400 +0200
@@ -71,7 +71,6 @@ control pipe(inout Headers_t headers, ou
             c1_Check_ip_0.apply();
             pass = pass_1;
             address = headers.ipv4.dstAddr;
-            pass_1 = pass;
             c1_Check_ip_0.apply();
             pass = pass_1;
         }
