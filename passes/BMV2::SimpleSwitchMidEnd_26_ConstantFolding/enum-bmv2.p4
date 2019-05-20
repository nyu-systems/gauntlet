*** dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:15.085578700 +0200
--- dumps/p4_16_samples/enum-bmv2.p4/pruned/enum-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:58:15.088751200 +0200
*************** control deparser(packet_out b, in Header
*** 35,44 ****
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      apply {
!         if (32w0 == 32w1) 
!             h.h.c = h.h.a;
!         else 
!             h.h.c = h.h.b;
          sm.egress_spec = 9w0;
      }
  }
--- 35,41 ----
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      apply {
!         h.h.c = h.h.b;
          sm.egress_spec = 9w0;
      }
  }
