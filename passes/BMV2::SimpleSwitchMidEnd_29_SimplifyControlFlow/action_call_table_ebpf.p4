*** dumps/p4_16_samples/action_call_table_ebpf.p4/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:57:46.527533600 +0200
--- dumps/p4_16_samples/action_call_table_ebpf.p4/pruned/action_call_table_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:57:46.531233700 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 9,25 ****
  }
  control pipe(inout Headers_t headers, out bool pass) {
      @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
!         {
!             {
!                 pass = (rej == 8w0 ? true : pass);
!                 pass = (!(rej == 8w0) ? false : pass);
!             }
!         }
!         {
!             {
!                 pass = (bar == 8w0 ? false : pass);
!             }
!         }
      }
      @name("pipe.t") table t {
          actions = {
--- 9,17 ----
  }
  control pipe(inout Headers_t headers, out bool pass) {
      @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
!         pass = (rej == 8w0 ? true : pass);
!         pass = (!(rej == 8w0) ? false : pass);
!         pass = (bar == 8w0 ? false : pass);
      }
      @name("pipe.t") table t {
          actions = {
