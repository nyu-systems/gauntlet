--- dumps/p4_16_samples/exit3.p4/pruned/exit3-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:42.465740000 +0200
+++ dumps/p4_16_samples/exit3.p4/pruned/exit3-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:42.468860400 +0200
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
