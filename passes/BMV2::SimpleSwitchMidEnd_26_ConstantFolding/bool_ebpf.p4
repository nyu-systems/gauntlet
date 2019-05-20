*** dumps/p4_16_samples/bool_ebpf.p4/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:59.541570600 +0200
--- dumps/p4_16_samples/bool_ebpf.p4/pruned/bool_ebpf-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:57:59.545366500 +0200
*************** parser prs(packet_in p, out Headers_t he
*** 9,15 ****
  }
  control pipe(inout Headers_t headers, out bool pass) {
      apply {
!         pass = true != false;
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
--- 9,15 ----
  }
  control pipe(inout Headers_t headers, out bool pass) {
      apply {
!         pass = true;
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
