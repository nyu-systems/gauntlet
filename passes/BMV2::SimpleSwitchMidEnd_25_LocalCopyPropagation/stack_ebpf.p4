--- dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:11.804763900 +0200
+++ dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:11.807221800 +0200
@@ -40,7 +40,6 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
-    bit<32> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("pipe.Reject") action Reject_0(IPv4Address add) {
@@ -49,7 +48,7 @@ control pipe(inout Headers_t headers, ou
     }
     @name("pipe.Check_src_ip") table Check_src_ip {
         key = {
-            key_0: exact @name("headers.ipv4[0].srcAddr") ;
+            headers.ipv4[0].srcAddr: exact @name("headers.ipv4[0].srcAddr") ;
         }
         actions = {
             Reject_0();
@@ -61,7 +60,6 @@ control pipe(inout Headers_t headers, ou
     apply {
         pass = true;
         {
-            key_0 = headers.ipv4[0].srcAddr;
             switch (Check_src_ip.apply().action_run) {
                 Reject_0: {
                     pass = false;
