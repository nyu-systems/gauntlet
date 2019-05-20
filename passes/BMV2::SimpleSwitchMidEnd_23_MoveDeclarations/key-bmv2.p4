--- dumps/p4_16_samples/key-bmv2.p4/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:31:19.999237000 +0200
+++ dumps/p4_16_samples/key-bmv2.p4/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:31:20.007803400 +0200
@@ -33,12 +33,12 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
+    bit<32> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingress.c.a") action c_a() {
         h.h.b = h.h.a;
     }
-    bit<32> key_0;
     @name("ingress.c.t") table c_t_0 {
         key = {
             key_0: exact @name("e") ;
