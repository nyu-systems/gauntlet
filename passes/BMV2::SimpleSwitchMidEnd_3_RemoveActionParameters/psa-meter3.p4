--- dumps/pruned/psa-meter3-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:33:21.682732000 +0200
+++ dumps/pruned/psa-meter3-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:21.684561900 +0200
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
