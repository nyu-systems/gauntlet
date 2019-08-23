--- before_pass
+++ after_pass
@@ -11,7 +11,10 @@ struct tuple_0 {
 control c() {
     tuple_0 x_0;
     apply {
-        x_0 = { 32w10, false };
+        {
+            x_0.field = 32w10;
+            x_0.field_0 = false;
+        }
     }
 }
 top(c()) main;
