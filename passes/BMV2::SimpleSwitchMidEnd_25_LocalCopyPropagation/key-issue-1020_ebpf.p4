--- dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:20.474267400 +0200
+++ dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:20.477109000 +0200
@@ -39,7 +39,6 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
-    bool tmp_0;
     bit<32> key_0;
     bit<32> key_1;
     @name("pipe.invalidate") action invalidate_0() {
@@ -68,7 +67,7 @@ control pipe(inout Headers_t headers, ou
         {
             key_0 = headers.ipv4.srcAddr + 32w1;
             key_1 = headers.ipv4.dstAddr + 32w1;
-            tmp_0 = t.apply().hit;
+            t.apply();
         }
     }
 }
