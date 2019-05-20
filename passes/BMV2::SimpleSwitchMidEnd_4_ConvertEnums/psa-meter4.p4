--- dumps/p4_16_samples/psa-meter4.p4/pruned/psa-meter4-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:49.094154300 +0200
+++ dumps/p4_16_samples/psa-meter4.p4/pruned/psa-meter4-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:31:49.096628900 +0200
@@ -22,7 +22,7 @@ parser MyEP(packet_in buffer, out EMPTY
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.meter0") DirectMeter(PSA_MeterType_t.PACKETS) meter0;
+    @name("MyIC.meter0") DirectMeter(32w0) meter0;
     @name("MyIC.tbl") table tbl {
         key = {
             a.srcAddr: exact @name("a.srcAddr") ;
