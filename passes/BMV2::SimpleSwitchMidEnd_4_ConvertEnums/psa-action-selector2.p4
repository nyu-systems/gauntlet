*** dumps/p4_16_samples/psa-action-selector2.p4/pruned/psa-action-selector2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:00.068594000 +0200
--- dumps/p4_16_samples/psa-action-selector2.p4/pruned/psa-action-selector2-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:00.070577500 +0200
*************** parser MyEP(packet_in buffer, out EMPTY
*** 26,32 ****
  control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
      @name(".NoAction") action NoAction_0() {
      }
!     @name("MyIC.as") ActionSelector(PSA_HashAlgorithm_t.CRC32, 32w1024, 32w16) as;
      @name("MyIC.a1") action a1_0() {
      }
      @name("MyIC.a2") action a2_0() {
--- 26,32 ----
  control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
      @name(".NoAction") action NoAction_0() {
      }
!     @name("MyIC.as") ActionSelector(32w1, 32w1024, 32w16) as;
      @name("MyIC.a1") action a1_0() {
      }
      @name("MyIC.a2") action a2_0() {
