--- before_pass
+++ after_pass
@@ -20,12 +20,11 @@ parser MyEP(packet_in buffer, out EMPTY
     }
 }
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
-    bit<10> tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("MyIC.reg") Register<bit<10>, bit<10>>(32w1024) reg;
     @name("MyIC.execute_register") action execute_register_0(bit<10> idx) {
-        tmp_0 = reg.read(idx);
+        reg.read(idx);
     }
     @name("MyIC.tbl") table tbl {
         key = {
