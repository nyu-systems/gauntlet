--- dumps/p4_16_samples/complex9.p4/pruned/complex9-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:23.228400600 +0200
+++ dumps/p4_16_samples/complex9.p4/pruned/complex9-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:23.231016500 +0200
@@ -1,19 +1,15 @@
 extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp_4;
-    bool tmp_5;
     bool tmp_6;
     bit<32> tmp_7;
-    bool tmp_8;
     apply {
         tmp_4 = f(32w2);
-        tmp_5 = tmp_4 > 32w0;
-        if (!tmp_5) 
+        if (!(tmp_4 > 32w0)) 
             tmp_6 = false;
         else {
             tmp_7 = f(32w3);
-            tmp_8 = tmp_7 < 32w0;
-            tmp_6 = tmp_8;
+            tmp_6 = tmp_7 < 32w0;
         }
         if (tmp_6) 
             r = 32w1;
