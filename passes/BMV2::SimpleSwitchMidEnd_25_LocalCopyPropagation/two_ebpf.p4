*** dumps/p4_16_samples/two_ebpf.p4/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:52.441392800 +0200
--- dumps/p4_16_samples/two_ebpf.p4/pruned/two_ebpf-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:52.446073500 +0200
*************** control pipe(inout Headers_t headers, ou
*** 71,77 ****
              c1_Check_ip_0.apply();
              pass = pass_1;
              address = headers.ipv4.dstAddr;
-             pass_1 = pass;
              c1_Check_ip_0.apply();
              pass = pass_1;
          }
--- 71,76 ----
