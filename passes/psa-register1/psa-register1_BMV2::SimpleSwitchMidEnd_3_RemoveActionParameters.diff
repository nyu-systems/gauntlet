--- before_pass
+++ after_pass
@@ -20,9 +20,9 @@ parser MyEP(packet_in buffer, out EMPTY
     }
 }
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
+    bit<10> tmp;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<10> tmp;
     @name("MyIC.reg") Register<bit<10>, bit<10>>(32w1024) reg_0;
     @name("MyIC.execute_register") action execute_register(bit<10> idx) {
         tmp = reg_0.read(idx);
