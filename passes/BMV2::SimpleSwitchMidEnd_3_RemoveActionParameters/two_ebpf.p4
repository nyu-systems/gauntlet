*** dumps/p4_16_samples/two_ebpf.p4/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:52.458081600 +0200
--- dumps/p4_16_samples/two_ebpf.p4/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:52.481425400 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 39,48 ****
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
-     @name(".NoAction") action NoAction_0() {
-     }
      IPv4Address address;
      bool pass_1;
      @name("pipe.c1.Reject") action c1_Reject() {
          pass_1 = false;
      }
--- 39,49 ----
      }
  }
  control pipe(inout Headers_t headers, out bool pass) {
      IPv4Address address;
      bool pass_1;
+     bool hasReturned_0;
+     @name(".NoAction") action NoAction_0() {
+     }
      @name("pipe.c1.Reject") action c1_Reject() {
          pass_1 = false;
      }
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
