*** dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:31.115621500 +0200
--- dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:31.119226500 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 40,46 ****
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
-     bit<32> key_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
--- 40,45 ----
*************** control pipe(inout Headers_t headers, ou
*** 49,55 ****
      }
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
!             key_0: exact @name("headers.ipv4[0].srcAddr") ;
          }
          actions = {
              Reject_0();
--- 48,54 ----
      }
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
!             headers.ipv4[0].srcAddr: exact @name("headers.ipv4[0].srcAddr") ;
          }
          actions = {
              Reject_0();
*************** control pipe(inout Headers_t headers, ou
*** 61,67 ****
      apply {
          pass = true;
          {
-             key_0 = headers.ipv4[0].srcAddr;
              switch (Check_src_ip.apply().action_run) {
                  Reject_0: {
                      pass = false;
--- 60,65 ----
