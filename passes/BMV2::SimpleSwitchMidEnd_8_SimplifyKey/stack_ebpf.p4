*** dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 17:00:31.175533500 +0200
--- dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 17:00:31.177965200 +0200
*************** control pipe(inout Headers_t headers, ou
*** 46,54 ****
          pass = false;
          headers.ipv4[0].srcAddr = add;
      }
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
!             headers.ipv4[0].srcAddr: exact @name("headers.ipv4[0].srcAddr") ;
          }
          actions = {
              Reject_0();
--- 46,55 ----
          pass = false;
          headers.ipv4[0].srcAddr = add;
      }
+     bit<32> key_0;
      @name("pipe.Check_src_ip") table Check_src_ip {
          key = {
!             key_0: exact @name("headers.ipv4[0].srcAddr") ;
          }
          actions = {
              Reject_0();
*************** control pipe(inout Headers_t headers, ou
*** 59,69 ****
      }
      apply {
          pass = true;
!         switch (Check_src_ip.apply().action_run) {
!             Reject_0: {
!                 pass = false;
!             }
!             NoAction_0: {
              }
          }
      }
--- 60,73 ----
      }
      apply {
          pass = true;
!         {
!             key_0 = headers.ipv4[0].srcAddr;
!             switch (Check_src_ip.apply().action_run) {
!                 Reject_0: {
!                     pass = false;
!                 }
!                 NoAction_0: {
!                 }
              }
          }
      }
