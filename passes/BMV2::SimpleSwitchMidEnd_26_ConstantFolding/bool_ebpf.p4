--- dumps/p4_16_samples/bool_ebpf.p4/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:14.490380700 +0200
+++ dumps/p4_16_samples/bool_ebpf.p4/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:14.492782500 +0200
@@ -9,7 +9,7 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     apply {
-        pass = true != false;
+        pass = true;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
