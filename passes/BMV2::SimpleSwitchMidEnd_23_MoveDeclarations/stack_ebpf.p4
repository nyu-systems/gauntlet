*** dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:00:31.108969500 +0200
--- dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:00:31.112182000 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 40,52 ****
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
      @name(".NoAction") action NoAction_0() {
      }
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
          pass = false;
          headers.ipv4[0].srcAddr = add;
      }
-     bit<32> key_0;
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
              key_0: exact @name("headers.ipv4[0].srcAddr") ;
--- 40,52 ----
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
+     bit<32> key_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
          pass = false;
          headers.ipv4[0].srcAddr = add;
      }
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
              key_0: exact @name("headers.ipv4[0].srcAddr") ;
