--- dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:31:20.465065000 +0200
+++ dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:31:20.471200100 +0200
@@ -40,6 +40,8 @@ parser prs(packet_in p, out Headers_t he
 }
 control pipe(inout Headers_t headers, out bool pass) {
     bool tmp_0;
+    bit<32> key_0;
+    bit<32> key_1;
     @name("pipe.invalidate") action invalidate_0() {
         headers.ipv4.setInvalid();
         headers.ethernet.setInvalid();
@@ -48,8 +50,6 @@ control pipe(inout Headers_t headers, ou
     @name("pipe.drop") action drop_0() {
         pass = false;
     }
-    bit<32> key_0;
-    bit<32> key_1;
     @name("pipe.t") table t {
         key = {
             key_0                   : exact @name(" headers.ipv4.srcAddr") ;
