--- dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:30:43.001114900 +0200
+++ dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:30:43.029641600 +0200
@@ -32,15 +32,19 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    @name("ingress.my_a") action my_a_0(bit<32> v) {
+    bit<32> v;
+    @name("ingress.my_a") action my_a_0() {
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
-        my_a_0(32w0);
-        my_a_2(32w1);
+        my_a_0();
+        my_a_2();
     }
 }
 V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
