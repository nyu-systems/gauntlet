--- before_pass
+++ after_pass
@@ -60,15 +60,31 @@ control Eg(inout Headers hdrs, inout Met
             val_0.field1 = 32w0;
         }
         _pred_0 = val_0.field1 != 32w0;
-        if (_pred_0) 
-            tmp = 32w1;
-        else 
-            tmp = 32w0;
+        {
+            bool cond;
+            {
+                bool pred;
+                cond = _pred_0;
+                pred = cond;
+                tmp = (pred ? 32w1 : tmp);
+                cond = !cond;
+                pred = cond;
+                tmp = (pred ? 32w0 : tmp);
+            }
+        }
         inc_0 = tmp;
-        if (_pred_0) 
-            tmp_0 = 32w1;
-        else 
-            tmp_0 = 32w0;
+        {
+            bool cond_0;
+            {
+                bool pred_0;
+                cond_0 = _pred_0;
+                pred_0 = cond_0;
+                tmp_0 = (pred_0 ? 32w1 : tmp_0);
+                cond_0 = !cond_0;
+                pred_0 = cond_0;
+                tmp_0 = (pred_0 ? 32w0 : tmp_0);
+            }
+        }
         debug_0.write(32w0, tmp_0);
         debug_0.write(32w1, inc_0);
         val_0.field1 = 32w1;
