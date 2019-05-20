--- dumps/p4_16_samples/issue870_ebpf.p4/pruned/issue870_ebpf-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:31:08.496611400 +0200
+++ dumps/p4_16_samples/issue870_ebpf.p4/pruned/issue870_ebpf-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:08.524752900 +0200
@@ -39,6 +39,7 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
+    bool hasReturned_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("pipe.Reject") action Reject_0(IPv4Address add) {
@@ -57,7 +58,7 @@ control pipe(inout Headers_t headers, ou
         const default_action = NoAction_0();
     }
     apply {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         pass = true;
         if (!headers.ipv4.isValid()) {
             pass = false;
