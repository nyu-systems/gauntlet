--- dumps/p4_16_samples/psa-counter1.p4/pruned/psa-counter1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:38.279877200 +0200
+++ dumps/p4_16_samples/psa-counter1.p4/pruned/psa-counter1-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:31:38.284681800 +0200
@@ -24,7 +24,7 @@ parser MyEP(packet_in buffer, out EMPTY
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.counter") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter;
+    @name("MyIC.counter") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter;
     @name("MyIC.execute") action execute_0() {
         counter.count(12w1024);
     }
