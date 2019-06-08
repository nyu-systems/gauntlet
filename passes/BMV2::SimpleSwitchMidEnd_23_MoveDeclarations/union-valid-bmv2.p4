--- before_pass
+++ after_pass
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
