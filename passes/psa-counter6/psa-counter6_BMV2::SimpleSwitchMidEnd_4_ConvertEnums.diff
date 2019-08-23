--- before_pass
+++ after_pass
@@ -24,7 +24,7 @@ control MyIC(inout ethernet_t a, inout E
     }
     @name(".NoAction") action NoAction_3() {
     }
-    @name("MyIC.counter0") DirectCounter<bit<12>>(PSA_CounterType_t.PACKETS) counter0_0;
+    @name("MyIC.counter0") DirectCounter<bit<12>>(32w0) counter0_0;
     @name("MyIC.execute") action execute_1() {
         counter0_0.count();
     }
