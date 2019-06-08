--- dumps/pruned/after-return-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:01.928696300 +0200
+++ dumps/pruned/after-return-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:01.931339600 +0200
@@ -1,13 +1,5 @@
 control ctrl() {
-    bit<32> a;
-    bool hasReturned_0;
     apply {
-        hasReturned_0 = false;
-        a = 32w0;
-        if (a == 32w0) 
-            hasReturned_0 = true;
-        else 
-            hasReturned_0 = true;
     }
 }
 control noop();
