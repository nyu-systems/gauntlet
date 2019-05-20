--- dumps/p4_16_samples/psa-action-selector2.p4/pruned/psa-action-selector2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:36.862313100 +0200
+++ dumps/p4_16_samples/psa-action-selector2.p4/pruned/psa-action-selector2-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:31:36.865060300 +0200
@@ -26,7 +26,7 @@ parser MyEP(packet_in buffer, out EMPTY
 control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.as") ActionSelector(PSA_HashAlgorithm_t.CRC32, 32w1024, 32w16) as;
+    @name("MyIC.as") ActionSelector(32w1, 32w1024, 32w16) as;
     @name("MyIC.a1") action a1_0() {
     }
     @name("MyIC.a2") action a2_0() {
