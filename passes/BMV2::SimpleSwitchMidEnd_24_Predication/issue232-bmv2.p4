--- before_pass
+++ after_pass
@@ -40,13 +40,21 @@ control Eg(inout Headers hdrs, inout Met
         }
         done_0 = false;
         ok_0 = !done_0 && same_0;
-        if (ok_0) {
+        {
+            bool cond;
             {
-                val_0.field1 = val.field1;
-            }
-            val_0.field1 = 32w8;
-            {
-                val.field1 = val_0.field1;
+                bool pred;
+                cond = ok_0;
+                pred = cond;
+                {
+                    {
+                        val_0.field1 = (pred ? val.field1 : val_0.field1);
+                    }
+                    val_0.field1 = (pred ? 32w8 : val_0.field1);
+                    {
+                        val.field1 = (pred ? val_0.field1 : val.field1);
+                    }
+                }
             }
         }
     }
