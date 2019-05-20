--- dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 17:30:36.961100800 +0200
+++ dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:30:36.967605500 +0200
@@ -60,15 +60,31 @@ control Eg(inout Headers hdrs, inout Met
             val.field1 = 32w0;
         }
         _pred = val.field1 != 32w0;
-        if (_pred) 
-            tmp_1 = 32w1;
-        else 
-            tmp_1 = 32w0;
+        {
+            bool cond;
+            {
+                bool pred;
+                cond = _pred;
+                pred = cond;
+                tmp_1 = (pred ? 32w1 : tmp_1);
+                cond = !cond;
+                pred = cond;
+                tmp_1 = (pred ? 32w0 : tmp_1);
+            }
+        }
         inc = tmp_1;
-        if (_pred) 
-            tmp_2 = 32w1;
-        else 
-            tmp_2 = 32w0;
+        {
+            bool cond_0;
+            {
+                bool pred_0;
+                cond_0 = _pred;
+                pred_0 = cond_0;
+                tmp_2 = (pred_0 ? 32w1 : tmp_2);
+                cond_0 = !cond_0;
+                pred_0 = cond_0;
+                tmp_2 = (pred_0 ? 32w0 : tmp_2);
+            }
+        }
         debug.write(32w0, tmp_2);
         debug.write(32w1, inc);
         val.field1 = 32w1;
