*** dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:43.293405300 +0200
--- dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:43.296458800 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 40,45 ****
--- 40,47 ----
  }
  control pipe(inout Headers_t headers, out bool pass) {
      bool tmp_0;
+     bit<32> key_0;
+     bit<32> key_1;
      @name("pipe.invalidate") action invalidate_0() {
          headers.ipv4.setInvalid();
          headers.ethernet.setInvalid();
*************** control pipe(inout Headers_t headers, ou
*** 48,55 ****
      @name("pipe.drop") action drop_0() {
          pass = false;
      }
-     bit<32> key_0;
-     bit<32> key_1;
      @name("pipe.t") table t {
          key = {
              key_0                   : exact @name(" headers.ipv4.srcAddr") ;
--- 50,55 ----
