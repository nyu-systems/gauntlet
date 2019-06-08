--- dumps/pruned/complex4-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:22.442102300 +0200
+++ dumps/pruned/complex4-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:22.444686600 +0200
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
