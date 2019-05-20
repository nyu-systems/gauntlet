*** dumps/p4_16_samples/psa-example-parser-checksum.p4/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:41.857317400 +0200
--- dumps/p4_16_samples/psa-example-parser-checksum.p4/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:41.867261900 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 97,107 ****
  }
  control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
      @name(".ingress_drop") action ingress_drop() {
!         {
!         }
!         {
!             ostd.drop = true;
!         }
      }
      @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts;
      @name("ingress.set_error_idx") action set_error_idx_0(ErrorIndex_t idx) {
--- 97,103 ----
  }
  control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
      @name(".ingress_drop") action ingress_drop() {
!         ostd.drop = true;
      }
      @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts;
      @name("ingress.set_error_idx") action set_error_idx_0(ErrorIndex_t idx) {
