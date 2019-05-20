--- dumps/p4_16_samples/exit1.p4/pruned/exit1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:41.752577600 +0200
+++ dumps/p4_16_samples/exit1.p4/pruned/exit1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:41.754976300 +0200
@@ -1,8 +1,6 @@
 control ctrl() {
-    bit<32> a;
     apply {
-        a = 32w0;
-        if (a == 32w0) 
+        if (32w0 == 32w0) 
             exit;
         else 
             exit;
