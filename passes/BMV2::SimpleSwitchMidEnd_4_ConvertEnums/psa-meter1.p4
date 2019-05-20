--- dumps/p4_16_samples/psa-meter1.p4/pruned/psa-meter1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:48.148303900 +0200
+++ dumps/p4_16_samples/psa-meter1.p4/pruned/psa-meter1-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:31:48.150674300 +0200
@@ -22,8 +22,8 @@ parser MyEP(packet_in buffer, out EMPTY
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.meter0") Meter<bit<12>>(32w1024, PSA_MeterType_t.PACKETS) meter0;
-    @name("MyIC.execute") action execute_0(bit<12> index, PSA_MeterColor_t color) {
+    @name("MyIC.meter0") Meter<bit<12>>(32w1024, 32w0) meter0;
+    @name("MyIC.execute") action execute_0(bit<12> index, bit<32> color) {
         meter0.execute(index, color);
     }
     @name("MyIC.tbl") table tbl {
