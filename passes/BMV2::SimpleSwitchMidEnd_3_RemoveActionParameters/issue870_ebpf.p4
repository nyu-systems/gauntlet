*** dumps/p4_16_samples/issue870_ebpf.p4/pruned/issue870_ebpf-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:30.388500400 +0200
--- dumps/p4_16_samples/issue870_ebpf.p4/pruned/issue870_ebpf-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:30.418362900 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 39,44 ****
--- 39,45 ----
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
+     bool hasReturned_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
*************** control pipe(inout Headers_t headers, ou
*** 57,63 ****
          const default_action = NoAction_0();
      }
      apply {
!         bool hasReturned_0 = false;
          pass = true;
          if (!headers.ipv4.isValid()) {
              pass = false;
--- 58,64 ----
          const default_action = NoAction_0();
      }
      apply {
!         hasReturned_0 = false;
          pass = true;
          if (!headers.ipv4.isValid()) {
              pass = false;
