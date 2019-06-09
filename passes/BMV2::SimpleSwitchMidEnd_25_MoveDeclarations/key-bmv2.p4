--- before_pass
+++ after_pass
@@ -33,12 +33,12 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
+    bit<32> key_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("ingress.c.a") action c_a_0() {
         h.h.b = h.h.a;
     }
-    bit<32> key_0;
     @name("ingress.c.t") table c_t {
         key = {
             key_0: exact @name("e") ;
