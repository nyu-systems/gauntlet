--- dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:00.588163400 +0200
+++ dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:00.591746200 +0200
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
