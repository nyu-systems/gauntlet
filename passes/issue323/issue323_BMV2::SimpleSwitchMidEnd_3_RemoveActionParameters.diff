--- before_pass
+++ after_pass
@@ -32,15 +32,19 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    @name("ingress.my_a") action my_a(bit<32> v) {
+    bit<32> v;
+    @name("ingress.my_a") action my_a() {
+        v = 32w0;
         h.h.f = v;
     }
-    @name("ingress.my_a") action my_a_2(bit<32> v_1) {
+    bit<32> v_1;
+    @name("ingress.my_a") action my_a_2() {
+        v_1 = 32w1;
         h.h.f = v_1;
     }
     apply {
-        my_a(32w0);
-        my_a_2(32w1);
+        my_a();
+        my_a_2();
     }
 }
 V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
