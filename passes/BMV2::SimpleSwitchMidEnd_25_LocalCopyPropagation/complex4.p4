--- dumps/p4_16_samples/complex4.p4/pruned/complex4-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:21.869601900 +0200
+++ dumps/p4_16_samples/complex4.p4/pruned/complex4-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:21.872235800 +0200
@@ -5,13 +5,11 @@ extern E {
 control c(inout bit<32> r) {
     bit<32> tmp_2;
     bit<32> tmp_3;
-    bit<32> tmp_4;
     @name("c.e") E() e_1;
     apply {
         tmp_2 = e_1.f(32w4);
         tmp_3 = e_1.f(32w5);
-        tmp_4 = tmp_2 + tmp_3;
-        r = tmp_4;
+        r = tmp_2 + tmp_3;
     }
 }
 control simple(inout bit<32> r);
