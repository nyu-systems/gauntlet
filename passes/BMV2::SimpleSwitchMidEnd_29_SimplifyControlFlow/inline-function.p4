--- dumps/pruned/inline-function-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:50.151909700 +0200
+++ dumps/pruned/inline-function-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:50.193169500 +0200
@@ -1,14 +1,10 @@
 control c(inout bit<32> x) {
     bit<32> tmp_6;
     apply {
-        {
-            {
-                if (x > x) 
-                    tmp_6 = x;
-                else 
-                    tmp_6 = x;
-            }
-        }
+        if (x > x) 
+            tmp_6 = x;
+        else 
+            tmp_6 = x;
         x = x + tmp_6;
     }
 }
