--- dumps/pruned/complex5-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:22.803281000 +0200
+++ dumps/pruned/complex5-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:22.805549500 +0200
@@ -1,11 +1,9 @@
 extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp_1;
-    bool tmp_2;
     apply {
         tmp_1 = f(32w2);
-        tmp_2 = tmp_1 > 32w0;
-        if (tmp_2) 
+        if (tmp_1 > 32w0) 
             r = 32w1;
         else 
             r = 32w2;
