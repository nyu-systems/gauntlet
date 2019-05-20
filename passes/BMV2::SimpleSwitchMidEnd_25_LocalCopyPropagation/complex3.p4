--- dumps/p4_16_samples/complex3.p4/pruned/complex3-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:21.585306100 +0200
+++ dumps/p4_16_samples/complex3.p4/pruned/complex3-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:21.587693200 +0200
@@ -2,12 +2,10 @@ extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp_2;
     bit<32> tmp_3;
-    bit<32> tmp_4;
     apply {
         tmp_2 = f(32w4);
         tmp_3 = f(32w5);
-        tmp_4 = tmp_2 + tmp_3;
-        r = tmp_4;
+        r = tmp_2 + tmp_3;
     }
 }
 control simple(inout bit<32> r);
