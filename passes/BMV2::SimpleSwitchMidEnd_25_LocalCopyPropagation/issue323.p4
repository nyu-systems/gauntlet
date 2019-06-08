--- dumps/pruned/issue323-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:23.073673400 +0200
+++ dumps/pruned/issue323-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:23.075840200 +0200
@@ -34,15 +34,11 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    bit<32> v;
-    bit<32> v_1;
     @name("ingress.my_a") action my_a_0() {
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
         my_a_0();
