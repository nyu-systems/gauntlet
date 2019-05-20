*** dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:34.649187400 +0200
--- dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:34.651692700 +0200
*************** control ComputeChecksumI(inout H hdr, in
*** 25,34 ****
  control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
      H hdr_1;
      apply {
!         hdr_1 = hdr;
!         hdr = hdr_1;
!         hdr_1 = hdr;
!         hdr = hdr_1;
      }
  }
  control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
--- 25,42 ----
  control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
      H hdr_1;
      apply {
!         {
!             hdr_1.stack = hdr.stack;
!         }
!         {
!             hdr.stack = hdr_1.stack;
!         }
!         {
!             hdr_1.stack = hdr.stack;
!         }
!         {
!             hdr.stack = hdr_1.stack;
!         }
      }
  }
  control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
