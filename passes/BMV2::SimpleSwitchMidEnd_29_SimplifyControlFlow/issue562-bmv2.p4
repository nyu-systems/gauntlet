*** dumps/p4_16_samples/issue562-bmv2.p4/pruned/issue562-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:21.775390500 +0200
--- dumps/p4_16_samples/issue562-bmv2.p4/pruned/issue562-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:21.835010600 +0200
*************** parser parse(packet_in pk, out parsed_pa
*** 20,29 ****
  }
  control ingress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
      apply {
!         {
!             local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
!             local_metadata.row.alt0.port = local_metadata.row.alt1.port;
!         }
          local_metadata.row.alt0.valid = 1w1;
          local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
          clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
--- 20,27 ----
  }
  control ingress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
      apply {
!         local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
!         local_metadata.row.alt0.port = local_metadata.row.alt1.port;
          local_metadata.row.alt0.valid = 1w1;
          local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
          clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
