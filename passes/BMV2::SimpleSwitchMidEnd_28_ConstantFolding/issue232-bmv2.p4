--- before_pass
+++ after_pass
@@ -26,9 +26,9 @@ control Eg(inout Headers hdrs, inout Met
             {
                 {
                     {
-                        val_0.field1 = (!false && 32w1 == 32w0 ? 32w0 : val_0.field1);
+                        val_0.field1 = val_0.field1;
                     }
-                    val_0.field1 = (!false && 32w1 == 32w0 ? 32w8 : val_0.field1);
+                    val_0.field1 = val_0.field1;
                 }
             }
         }
