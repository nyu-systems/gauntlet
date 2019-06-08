--- dumps/pruned/psa-hash-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:33:20.409043400 +0200
+++ dumps/pruned/psa-hash-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:20.441229300 +0200
@@ -23,9 +23,9 @@ parser MyEP(packet_in buffer, out EMPTY
     }
 }
 control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
+    bit<16> tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<16> tmp_0;
     @name("MyIC.h") Hash<bit<16>>(PSA_HashAlgorithm_t.CRC16) h;
     @name("MyIC.a1") action a1_0() {
         tmp_0 = h.get_hash<ethernet_t>(a);
