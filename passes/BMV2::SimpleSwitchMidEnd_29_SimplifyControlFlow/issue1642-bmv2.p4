*** dumps/p4_16_samples/issue1642-bmv2.p4/pruned/issue1642-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:51.724088000 +0200
--- dumps/p4_16_samples/issue1642-bmv2.p4/pruned/issue1642-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:51.783660700 +0200
*************** control ingress(inout parsed_packet_t hd
*** 26,35 ****
      apply {
          local_metadata.s.setValid();
          local_metadata.s.f = 32w0;
!         {
!             local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
!             local_metadata.row.alt0.port = local_metadata.row.alt1.port;
!         }
          local_metadata.row.alt0.valid = 1w1;
          local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
          clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
--- 26,33 ----
      apply {
          local_metadata.s.setValid();
          local_metadata.s.f = 32w0;
!         local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
!         local_metadata.row.alt0.port = local_metadata.row.alt1.port;
          local_metadata.row.alt0.valid = 1w1;
          local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
          clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
