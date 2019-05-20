*** dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:15.081186900 +0200
--- dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:15.085578700 +0200
*************** control deparser(packet_out b, in Header
*** 34,43 ****
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-     bit<32> c_c_0;
      apply {
!         c_c_0 = 32w0;
!         if (c_c_0 == 32w1) 
              h.h.c = h.h.a;
          else 
              h.h.c = h.h.b;
--- 34,41 ----
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      apply {
!         if (32w0 == 32w1) 
              h.h.c = h.h.a;
          else 
              h.h.c = h.h.b;
