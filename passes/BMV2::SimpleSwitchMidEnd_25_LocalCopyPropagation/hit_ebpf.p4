*** dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:31.165157500 +0200
--- dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:31.167578300 +0200
*************** control pipe(inout Headers_t headers, ou
*** 67,74 ****
          }
          if (!hasReturned_0) {
              tmp_0 = Check_src_ip.apply().hit;
-             if (tmp_0) 
-                 pass = pass;
          }
      }
  }
--- 67,72 ----
