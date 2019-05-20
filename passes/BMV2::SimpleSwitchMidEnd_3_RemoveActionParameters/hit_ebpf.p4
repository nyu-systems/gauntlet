--- dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:29:59.162526800 +0200
+++ dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:29:59.183361300 +0200
@@ -39,9 +39,10 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
+    bool tmp_0;
+    bool hasReturned_0;
     @name(".NoAction") action NoAction_0() {
     }
-    bool tmp_0;
     @name("pipe.Reject") action Reject_0(IPv4Address add) {
         pass = false;
         headers.ipv4.srcAddr = add;
@@ -58,7 +59,7 @@ control pipe(inout Headers_t headers, ou
         const default_action = NoAction_0();
     }
     apply {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         pass = true;
         if (!headers.ipv4.isValid()) {
             pass = false;
