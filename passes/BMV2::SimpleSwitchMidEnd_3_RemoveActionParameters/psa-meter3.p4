--- dumps/p4_16_samples/psa-meter3.p4/pruned/psa-meter3-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:31:48.628341600 +0200
+++ dumps/p4_16_samples/psa-meter3.p4/pruned/psa-meter3-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:48.631322500 +0200
@@ -20,10 +20,10 @@ parser MyEP(packet_in buffer, out EMPTY
     }
 }
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
-    @name(".NoAction") action NoAction_0() {
-    }
     PSA_MeterColor_t tmp_1;
     bool tmp_2;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("MyIC.meter0") Meter<bit<12>>(32w1024, PSA_MeterType_t.PACKETS) meter0;
     @name("MyIC.tbl") table tbl {
         key = {
