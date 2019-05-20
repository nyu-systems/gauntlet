*** dumps/p4_16_samples/psa-portid-using-newtype2.p4/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:15.642102300 +0200
--- dumps/p4_16_samples/psa-portid-using-newtype2.p4/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:00:15.646924700 +0200
*************** control FabricIngress(inout parsed_heade
*** 161,167 ****
          filtering_t_0.apply();
          forwarding_t_0.apply();
          standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec + 9w1;
!         standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec & (PortIdUInt_t)9w0xf;
      }
  }
  control FabricEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
--- 161,167 ----
          filtering_t_0.apply();
          forwarding_t_0.apply();
          standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec + 9w1;
!         standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec & 9w0xf;
      }
  }
  control FabricEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
