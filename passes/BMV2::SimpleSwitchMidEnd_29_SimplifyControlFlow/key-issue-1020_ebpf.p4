*** dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:43.312031300 +0200
--- dumps/p4_16_samples/key-issue-1020_ebpf.p4/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:43.314716400 +0200
*************** control pipe(inout Headers_t headers, ou
*** 64,74 ****
          default_action = drop_0();
      }
      apply {
!         {
!             key_0 = headers.ipv4.srcAddr + 32w1;
!             key_1 = headers.ipv4.dstAddr + 32w1;
!             t.apply();
!         }
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
--- 64,72 ----
          default_action = drop_0();
      }
      apply {
!         key_0 = headers.ipv4.srcAddr + 32w1;
!         key_1 = headers.ipv4.dstAddr + 32w1;
!         t.apply();
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
