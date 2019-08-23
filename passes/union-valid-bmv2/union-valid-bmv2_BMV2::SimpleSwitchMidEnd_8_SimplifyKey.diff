--- before_pass
+++ after_pass
@@ -50,9 +50,10 @@ control deparser(packet_out b, in Header
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     @name("ingress.a") action a_1() {
     }
+    bool key_0;
     @name("ingress.t") table t_0 {
         key = {
-            h.u.isValid(): exact @name("h.u.$valid$") ;
+            key_0: exact @name("h.u.$valid$") ;
         }
         actions = {
             a_1();
@@ -60,7 +61,10 @@ control ingress(inout Headers h, inout M
         default_action = a_1();
     }
     apply {
-        t_0.apply();
+        {
+            key_0 = h.u.isValid();
+            t_0.apply();
+        }
     }
 }
 V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
