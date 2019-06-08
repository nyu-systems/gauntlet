--- before_pass
+++ after_pass
@@ -9,11 +9,8 @@ struct tuple_0 {
     bool    field_0;
 }
 control c() {
-    tuple_0 x;
     apply {
         {
-            x.field = 32w10;
-            x.field_0 = false;
         }
     }
 }
