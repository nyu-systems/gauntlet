--- before_pass
+++ after_pass
@@ -24,7 +24,7 @@ control MyIC(inout ethernet_t a, inout E
     }
     @name(".NoAction") action NoAction_3() {
     }
-    @name("MyIC.meter0") DirectMeter(PSA_MeterType_t.PACKETS) meter0;
+    @name("MyIC.meter0") DirectMeter(32w0) meter0;
     @name("MyIC.execute_meter") action execute_meter_0() {
         meter0.execute();
     }
