--- dumps/pruned/exit1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:36.048562600 +0200
+++ dumps/pruned/exit1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:36.052224600 +0200
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
