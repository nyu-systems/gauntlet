*** dumps/p4_16_samples/std_meta_inlining.p4/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:32.453317000 +0200
--- dumps/p4_16_samples/std_meta_inlining.p4/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:32.455638400 +0200
*************** control DeparserImpl(packet_out packet,
*** 15,25 ****
  }
  control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
      @name(".send_to_cpu") action send_to_cpu() {
!         {
!         }
!         {
!             standard_metadata.egress_spec = 9w64;
!         }
      }
      @name(".NoAction") action NoAction_0() {
      }
--- 15,21 ----
  }
  control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
      @name(".send_to_cpu") action send_to_cpu() {
!         standard_metadata.egress_spec = 9w64;
      }
      @name(".NoAction") action NoAction_0() {
      }
