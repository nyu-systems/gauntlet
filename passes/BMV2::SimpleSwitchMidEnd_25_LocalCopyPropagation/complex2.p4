--- dumps/pruned/complex2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:21.535653800 +0200
+++ dumps/pruned/complex2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:21.544113400 +0200
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
