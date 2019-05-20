*** dumps/p4_16_samples/psa-example-parser-checksum.p4/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:41.640606300 +0200
--- dumps/p4_16_samples/psa-example-parser-checksum.p4/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:41.753547900 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 83,90 ****
      }
  }
  control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
!     @name(".ingress_drop") action ingress_drop(inout psa_ingress_output_metadata_t meta_1) {
          meta_1.drop = true;
      }
      @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS) parser_error_counts;
      @name("ingress.set_error_idx") action set_error_idx_0(ErrorIndex_t idx) {
--- 83,93 ----
      }
  }
  control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
!     psa_ingress_output_metadata_t meta_1;
!     @name(".ingress_drop") action ingress_drop() {
!         meta_1 = ostd;
          meta_1.drop = true;
+         ostd = meta_1;
      }
      @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(PSA_CounterType_t.PACKETS) parser_error_counts;
      @name("ingress.set_error_idx") action set_error_idx_0(ErrorIndex_t idx) {
*************** control ingress(inout headers hdr, inout
*** 113,119 ****
      apply {
          if (istd.parser_error != error.NoError) {
              parser_error_count_and_convert.apply();
!             ingress_drop(ostd);
              exit;
          }
      }
--- 116,122 ----
      apply {
          if (istd.parser_error != error.NoError) {
              parser_error_count_and_convert.apply();
!             ingress_drop();
              exit;
          }
      }
