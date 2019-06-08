--- dumps/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:14.031879500 +0200
+++ dumps/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:14.034232300 +0200
@@ -8,10 +8,8 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
-    bool x;
     apply {
-        x = true;
-        pass = x != false;
+        pass = true != false;
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
