--- dumps/p4_16_samples/complex2.p4/pruned/complex2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:21.227564400 +0200
+++ dumps/p4_16_samples/complex2.p4/pruned/complex2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:21.230595900 +0200
@@ -5,11 +5,9 @@ header H {
 control c(inout bit<32> r) {
     H[2] h;
     bit<32> tmp_1;
-    bit<32> tmp_2;
     apply {
         tmp_1 = f(32w2);
-        tmp_2 = tmp_1;
-        h[tmp_2].setValid();
+        h[tmp_1].setValid();
     }
 }
 control simple(inout bit<32> r);
