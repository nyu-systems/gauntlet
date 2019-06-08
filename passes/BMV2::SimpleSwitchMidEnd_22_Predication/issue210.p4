--- dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-06-08 18:32:17.266882300 +0200
+++ dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:17.270589800 +0200
@@ -2,10 +2,18 @@
 control Ing(out bit<32> a) {
     bool b;
     @name("Ing.cond") action cond_0() {
-        if (b) 
-            a = 32w5;
-        else 
-            a = 32w10;
+        {
+            bool cond;
+            {
+                bool pred;
+                cond = b;
+                pred = cond;
+                a = (pred ? 32w5 : a);
+                cond = !cond;
+                pred = cond;
+                a = (pred ? 32w10 : a);
+            }
+        }
     }
     apply {
         b = true;
