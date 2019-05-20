*** dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_30_CompileTimeOperations.p4	2019-05-20 16:58:31.183077600 +0200
--- dumps/p4_16_samples/hit_ebpf.p4/pruned/hit_ebpf-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 16:58:31.185955400 +0200
*************** control pipe(inout Headers_t headers, ou
*** 66,72 ****
              hasReturned_0 = true;
          }
          if (!hasReturned_0) 
!             tmp_0 = Check_src_ip.apply().hit;
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
--- 66,75 ----
              hasReturned_0 = true;
          }
          if (!hasReturned_0) 
!             if (Check_src_ip.apply().hit) 
!                 tmp_0 = true;
!             else 
!                 tmp_0 = false;
      }
  }
  ebpfFilter<Headers_t>(prs(), pipe()) main;
