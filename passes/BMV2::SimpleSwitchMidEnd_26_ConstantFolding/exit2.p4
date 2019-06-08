--- dumps/pruned/exit2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:36.431651300 +0200
+++ dumps/pruned/exit2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:36.435085800 +0200
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
