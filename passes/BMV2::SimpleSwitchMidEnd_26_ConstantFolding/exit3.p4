--- dumps/pruned/exit3-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:36.846078500 +0200
+++ dumps/pruned/exit3-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:36.849780000 +0200
@@ -10,10 +10,7 @@ control ctrl(out bit<32> c) {
     }
     apply {
         c = 32w2;
-        if (32w0 == 32w0) 
-            t.apply();
-        else 
-            t.apply();
+        t.apply();
         c = 32w5;
     }
 }
