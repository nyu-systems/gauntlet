*** dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:34.651692700 +0200
--- dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:58:34.654490200 +0200
*************** control ComputeChecksumI(inout H hdr, in
*** 23,41 ****
      }
  }
  control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
!     H hdr_1;
      apply {
          {
!             hdr_1.stack = hdr.stack;
          }
          {
!             hdr.stack = hdr_1.stack;
          }
          {
!             hdr_1.stack = hdr.stack;
          }
          {
!             hdr.stack = hdr_1.stack;
          }
      }
  }
--- 23,41 ----
      }
  }
  control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
!     h_t[1] hdr_1_stack;
      apply {
          {
!             hdr_1_stack = hdr.stack;
          }
          {
!             hdr.stack = hdr_1_stack;
          }
          {
!             hdr_1_stack = hdr.stack;
          }
          {
!             hdr.stack = hdr_1_stack;
          }
      }
  }
