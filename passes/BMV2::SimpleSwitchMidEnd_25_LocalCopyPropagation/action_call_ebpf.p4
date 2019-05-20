*** dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:46.146271600 +0200
--- dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:46.149380700 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 9,18 ****
  }
  control pipe(inout Headers_t headers, out bool pass) {
      bool x;
-     bool rej;
      @name("pipe.Reject") action Reject_0() {
!         rej = x;
!         pass = rej;
      }
      apply {
          x = true;
--- 9,16 ----
  }
  control pipe(inout Headers_t headers, out bool pass) {
      bool x;
      @name("pipe.Reject") action Reject_0() {
!         pass = x;
      }
      apply {
          x = true;
