--- before_pass
+++ after_pass
@@ -22,8 +22,8 @@ parser MyEP(packet_in buffer, out EMPTY
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.counter0") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter0;
-    @name("MyIC.counter1") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter1;
+    @name("MyIC.counter0") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter0;
+    @name("MyIC.counter1") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter1;
     @name("MyIC.execute") action execute_0() {
         counter0.count(12w1024);
         counter1.count(12w1024);
