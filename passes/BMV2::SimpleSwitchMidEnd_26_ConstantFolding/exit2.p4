--- dumps/p4_16_samples/exit2.p4/pruned/exit2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:42.121120100 +0200
+++ dumps/p4_16_samples/exit2.p4/pruned/exit2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:42.126946300 +0200
@@ -7,10 +7,7 @@ control ctrl(out bit<32> c) {
     }
     apply {
         c = 32w2;
-        if (32w0 == 32w0) 
-            e_0();
-        else 
-            e_2();
+        e_0();
         c = 32w5;
     }
 }
