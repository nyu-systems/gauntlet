--- dumps/pruned/exit1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:36.052224600 +0200
+++ dumps/pruned/exit1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:36.055909600 +0200
@@ -1,9 +1,6 @@
 control ctrl() {
     apply {
-        if (32w0 == 32w0) 
-            exit;
-        else 
-            exit;
+        exit;
     }
 }
 control noop();
