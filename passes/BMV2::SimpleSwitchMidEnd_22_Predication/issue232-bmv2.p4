--- before_pass
+++ after_pass
@@ -40,13 +40,21 @@ control Eg(inout Headers hdrs, inout Met
         }
         done = false;
         ok = !done && same;
-        if (ok) {
+        {
+            bool cond;
             {
-                val_2.field1 = val_1.field1;
-            }
-            val_2.field1 = 32w8;
-            {
-                val_1.field1 = val_2.field1;
+                bool pred;
+                cond = ok;
+                pred = cond;
+                {
+                    {
+                        val_2.field1 = (pred ? val_1.field1 : val_2.field1);
+                    }
+                    val_2.field1 = (pred ? 32w8 : val_2.field1);
+                    {
+                        val_1.field1 = (pred ? val_2.field1 : val_1.field1);
+                    }
+                }
             }
         }
     }
