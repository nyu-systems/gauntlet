--- dumps/pruned/psa-meter1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:21.261234900 +0200
+++ dumps/pruned/psa-meter1-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:33:21.263961200 +0200
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
