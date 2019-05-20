--- dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:29:00.603202300 +0200
+++ dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:29:00.626584900 +0200
@@ -9,12 +9,14 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool x;
-    @name("pipe.Reject") action Reject_0(bool rej) {
+    bool rej;
+    @name("pipe.Reject") action Reject_0() {
+        rej = x;
         pass = rej;
     }
     apply {
         x = true;
-        Reject_0(x);
+        Reject_0();
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
