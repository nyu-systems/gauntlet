--- before_pass
+++ after_pass
@@ -8,10 +8,8 @@ struct tuple_0 {
 control c() {
     tuple_0 x;
     apply {
-        {
-            x.field = 32w10;
-            x.field_0 = false;
-        }
+        x.field = 32w10;
+        x.field_0 = false;
         f<tuple_0>(x);
     }
 }
