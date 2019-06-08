--- dumps/pruned/psa-counter6-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:14.019220500 +0200
+++ dumps/pruned/psa-counter6-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:33:14.024999700 +0200
@@ -24,7 +24,7 @@ control MyIC(inout ethernet_t a, inout E
     }
     @name(".NoAction") action NoAction_3() {
     }
-    @name("MyIC.counter0") DirectCounter<bit<12>>(PSA_CounterType_t.PACKETS) counter0;
+    @name("MyIC.counter0") DirectCounter<bit<12>>(32w0) counter0;
     @name("MyIC.execute") action execute_0() {
         counter0.count();
     }
