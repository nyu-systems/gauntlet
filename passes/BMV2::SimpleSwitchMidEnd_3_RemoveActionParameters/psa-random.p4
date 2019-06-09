--- before_pass
+++ after_pass
@@ -23,9 +23,9 @@ parser MyEP(packet_in buffer, out EMPTY
     }
 }
 control MyIC(inout ethernet_t a, inout user_meta_t b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
+    bit<16> tmp;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<16> tmp;
     @name("MyIC.rand") Random<bit<16>>(16w200, 16w400) rand_0;
     @name("MyIC.execute_random") action execute_random() {
         tmp = rand_0.read();
