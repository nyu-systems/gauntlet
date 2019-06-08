--- dumps/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:34:21.174126100 +0200
+++ dumps/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:34:21.177496900 +0200
@@ -51,9 +51,9 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
+    bool key_0;
     @name("ingress.a") action a_0() {
     }
-    bool key_0;
     @name("ingress.t") table t {
         key = {
             key_0: exact @name("h.u.$valid$") ;
