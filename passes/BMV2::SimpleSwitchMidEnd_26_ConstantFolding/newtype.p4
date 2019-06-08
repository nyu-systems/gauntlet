--- dumps/pruned/newtype-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:00.617546100 +0200
+++ dumps/pruned/newtype-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:33:00.619998900 +0200
@@ -23,12 +23,10 @@ control c(out B32 x) {
     }
     apply {
         k = 32w0;
-        x = (B32)32w0;
-        if (32w0 == 32w1) 
-            x = 32w2;
+        x = 32w0;
+        ;
         t.apply();
-        if (32w0 == (B32)32w0) 
-            x = 32w3;
+        x = 32w3;
     }
 }
 control e(out B32 x);
