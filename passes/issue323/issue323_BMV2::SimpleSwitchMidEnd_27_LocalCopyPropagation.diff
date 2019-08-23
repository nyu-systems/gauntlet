--- before_pass
+++ after_pass
@@ -34,15 +34,11 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    bit<32> v;
-    bit<32> v_1;
     @name("ingress.my_a") action my_a() {
-        v = 32w0;
-        h.h.f = v;
+        h.h.f = 32w0;
     }
     @name("ingress.my_a") action my_a_2() {
-        v_1 = 32w1;
-        h.h.f = v_1;
+        h.h.f = 32w1;
     }
     apply {
         my_a();
