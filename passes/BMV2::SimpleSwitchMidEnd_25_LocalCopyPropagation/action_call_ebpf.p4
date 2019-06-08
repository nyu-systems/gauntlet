--- dumps/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:00.362235300 +0200
+++ dumps/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:00.364381300 +0200
@@ -9,10 +9,8 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool x;
-    bool rej;
     @name("pipe.Reject") action Reject_0() {
-        rej = x;
-        pass = rej;
+        pass = x;
     }
     apply {
         x = true;
