--- dumps/pruned/psa-meter6-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:23.893077000 +0200
+++ dumps/pruned/psa-meter6-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:33:23.895619500 +0200
@@ -24,7 +24,7 @@ control MyIC(inout ethernet_t a, inout E
     }
     @name(".NoAction") action NoAction_3() {
     }
-    @name("MyIC.meter0") DirectMeter(PSA_MeterType_t.PACKETS) meter0;
+    @name("MyIC.meter0") DirectMeter(32w0) meter0;
     @name("MyIC.execute_meter") action execute_meter_0() {
         meter0.execute();
     }
