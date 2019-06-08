--- dumps/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:14.034232300 +0200
+++ dumps/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:14.036530700 +0200
@@ -9,7 +9,7 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     apply {
-        pass = true != false;
+        pass = true;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
