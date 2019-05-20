--- dumps/p4_16_samples/psa-register1.p4/pruned/psa-register1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:31:54.166403700 +0200
+++ dumps/p4_16_samples/psa-register1.p4/pruned/psa-register1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:54.192091600 +0200
@@ -20,9 +20,9 @@ parser MyEP(packet_in buffer, out EMPTY
     }
 }
 control MyIC(inout ethernet_t a, inout EMPTY b, in psa_ingress_input_metadata_t c, inout psa_ingress_output_metadata_t d) {
+    bit<10> tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<10> tmp_0;
     @name("MyIC.reg") Register<bit<10>, bit<10>>(32w1024) reg;
     @name("MyIC.execute_register") action execute_register_0(bit<10> idx) {
         tmp_0 = reg.read(idx);
