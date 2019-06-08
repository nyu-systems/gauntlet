--- dumps/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:18.709399000 +0200
+++ dumps/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:18.711991600 +0200
@@ -71,7 +71,6 @@ control pipe(inout Headers_t headers, ou
             c1_Check_ip_0.apply();
             pass = pass_1;
             address = headers.ipv4.dstAddr;
-            pass_1 = pass;
             c1_Check_ip_0.apply();
             pass = pass_1;
         }
