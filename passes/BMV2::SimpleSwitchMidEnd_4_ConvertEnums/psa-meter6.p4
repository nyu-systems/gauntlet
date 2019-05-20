--- dumps/p4_16_samples/psa-meter6.p4/pruned/psa-meter6-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:50.306175100 +0200
+++ dumps/p4_16_samples/psa-meter6.p4/pruned/psa-meter6-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:31:50.308455800 +0200
@@ -24,7 +24,7 @@ control MyIC(inout ethernet_t a, inout E
     }
     @name(".NoAction") action NoAction_3() {
     }
-    @name("MyIC.meter0") DirectMeter(PSA_MeterType_t.PACKETS) meter0;
+    @name("MyIC.meter0") DirectMeter(32w0) meter0;
     @name("MyIC.execute_meter") action execute_meter_0() {
         meter0.execute();
     }
