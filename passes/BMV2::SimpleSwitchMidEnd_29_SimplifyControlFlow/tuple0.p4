--- before_pass
+++ after_pass
@@ -8,10 +8,8 @@ package top(proto _p);
 control c() {
     tuple_0 x;
     apply {
-        {
-            x.field = 32w10;
-            x.field_0 = false;
-        }
+        x.field = 32w10;
+        x.field_0 = false;
         f(x);
         f({ 32w20, true });
     }
