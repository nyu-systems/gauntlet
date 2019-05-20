*** dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:57:46.159773800 +0200
--- dumps/p4_16_samples/action_call_ebpf.p4/pruned/action_call_ebpf-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:57:46.184413300 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 9,20 ****
  }
  control pipe(inout Headers_t headers, out bool pass) {
      bool x;
!     @name("pipe.Reject") action Reject_0(bool rej) {
          pass = rej;
      }
      apply {
          x = true;
!         Reject_0(x);
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
--- 9,22 ----
  }
  control pipe(inout Headers_t headers, out bool pass) {
      bool x;
!     bool rej;
!     @name("pipe.Reject") action Reject_0() {
!         rej = x;
          pass = rej;
      }
      apply {
          x = true;
!         Reject_0();
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
