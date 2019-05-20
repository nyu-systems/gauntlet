*** dumps/p4_16_samples/issue1642-bmv2.p4/pruned/issue1642-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:51.693586200 +0200
--- dumps/p4_16_samples/issue1642-bmv2.p4/pruned/issue1642-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:51.697973100 +0200
*************** control ingress(inout parsed_packet_t hd
*** 26,32 ****
      apply {
          local_metadata.s.setValid();
          local_metadata.s.f = 32w0;
!         local_metadata.row.alt0 = local_metadata.row.alt1;
          local_metadata.row.alt0.valid = 1w1;
          local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
          clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
--- 26,35 ----
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
