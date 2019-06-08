--- before_pass
+++ after_pass
@@ -32,9 +32,9 @@ control Eg(inout Headers hdrs, inout Met
             {
                 {
                     {
-                        val_2.field1 = (!false && 32w1 == 32w0 ? 32w0 : val_2.field1);
+                        val_2.field1 = val_2.field1;
                     }
-                    val_2.field1 = (!false && 32w1 == 32w0 ? 32w8 : val_2.field1);
+                    val_2.field1 = val_2.field1;
                     {
                     }
                 }
