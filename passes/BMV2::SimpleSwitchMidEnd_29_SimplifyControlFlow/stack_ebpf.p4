*** dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:31.127771300 +0200
--- dumps/p4_16_samples/stack_ebpf.p4/pruned/stack_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:31.130225400 +0200
*************** control pipe(inout Headers_t headers, ou
*** 59,71 ****
      }
      apply {
          pass = true;
!         {
!             switch (Check_src_ip.apply().action_run) {
!                 Reject_0: {
!                     pass = false;
!                 }
!                 NoAction_0: {
!                 }
              }
          }
      }
--- 59,69 ----
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
