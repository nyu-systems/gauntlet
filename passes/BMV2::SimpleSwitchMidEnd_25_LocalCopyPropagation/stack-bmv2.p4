*** dumps/p4_16_samples/stack-bmv2.p4/pruned/stack-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:29.636405900 +0200
--- dumps/p4_16_samples/stack-bmv2.p4/pruned/stack-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:29.638368600 +0200
*************** control deparser(packet_out b, in Header
*** 32,41 ****
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-     hdr[1] c_tmp_0;
      apply {
!         c_tmp_0[0].f = h.h.f + 32w1;
!         h.h.f = c_tmp_0[0].f;
          sm.egress_spec = 9w0;
      }
  }
--- 32,39 ----
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      apply {
!         h.h.f = h.h.f + 32w1;
          sm.egress_spec = 9w0;
      }
  }
