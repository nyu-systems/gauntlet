--- before_pass
+++ after_pass
@@ -5,8 +5,14 @@ struct S {
 control c(out bit<1> b) {
     S s;
     apply {
-        s = { 1w0, 1w1 };
-        s = { s.b, s.a };
+        {
+            s.a = 1w0;
+            s.b = 1w1;
+        }
+        {
+            s.a = s.b;
+            s.b = s.a;
+        }
         b = s.a;
     }
 }
