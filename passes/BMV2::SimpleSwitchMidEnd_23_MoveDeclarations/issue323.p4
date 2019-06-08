--- before_pass
+++ after_pass
@@ -35,11 +35,11 @@ control deparser(packet_out b, in Header
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     bit<32> v;
+    bit<32> v_1;
     @name("ingress.my_a") action my_a_0() {
         v = 32w0;
         h.h.f = v;
     }
-    bit<32> v_1;
     @name("ingress.my_a") action my_a_2() {
         v_1 = 32w1;
         h.h.f = v_1;
