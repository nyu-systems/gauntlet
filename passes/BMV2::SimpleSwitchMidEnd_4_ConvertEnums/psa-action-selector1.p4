--- before_pass
+++ after_pass
@@ -25,7 +25,7 @@ parser MyEP(packet_in buffer, out EMPTY
 control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.as") ActionSelector(PSA_HashAlgorithm_t.CRC32, 32w1024, 32w16) as_0;
+    @name("MyIC.as") ActionSelector(32w1, 32w1024, 32w16) as_0;
     @name("MyIC.a1") action a1() {
     }
     @name("MyIC.a2") action a2() {
