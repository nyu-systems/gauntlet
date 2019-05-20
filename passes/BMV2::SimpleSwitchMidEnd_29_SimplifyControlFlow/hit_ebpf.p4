*** dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:31.177765900 +0200
--- dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:31.233728500 +0200
*************** control pipe(inout Headers_t headers, ou
*** 65,73 ****
              pass = false;
              hasReturned_0 = true;
          }
!         if (!hasReturned_0) {
              tmp_0 = Check_src_ip.apply().hit;
-         }
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
--- 65,72 ----
              pass = false;
              hasReturned_0 = true;
          }
!         if (!hasReturned_0) 
              tmp_0 = Check_src_ip.apply().hit;
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
