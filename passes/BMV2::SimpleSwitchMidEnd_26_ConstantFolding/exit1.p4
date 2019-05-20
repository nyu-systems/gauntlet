--- dumps/p4_16_samples/exit1.p4/pruned/exit1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:41.754976300 +0200
+++ dumps/p4_16_samples/exit1.p4/pruned/exit1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:41.761504300 +0200
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
