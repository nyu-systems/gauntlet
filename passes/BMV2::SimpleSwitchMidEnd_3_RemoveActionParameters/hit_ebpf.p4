*** dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:31.180613200 +0200
--- dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:31.204682000 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 39,47 ****
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
      @name(".NoAction") action NoAction_0() {
      }
-     bool tmp_0;
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
          pass = false;
          headers.ipv4.srcAddr = add;
--- 39,48 ----
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
+     bool tmp_0;
+     bool hasReturned_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("pipe.Reject") action Reject_0(IPv4Address add) {
          pass = false;
          headers.ipv4.srcAddr = add;
*************** control pipe(inout Headers_t headers, ou
*** 58,64 ****
          const default_action = NoAction_0();
      }
      apply {
!         bool hasReturned_0 = false;
          pass = true;
          if (!headers.ipv4.isValid()) {
              pass = false;
--- 59,65 ----
          const default_action = NoAction_0();
      }
      apply {
!         hasReturned_0 = false;
          pass = true;
          if (!headers.ipv4.isValid()) {
              pass = false;
