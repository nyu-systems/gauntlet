--- before_pass
+++ after_pass
@@ -3,22 +3,8 @@ struct S {
     bit<1> b;
 }
 control c(out bit<1> b) {
-    S s_0;
-    S tmp;
     apply {
-        {
-            s_0.a = 1w0;
-            s_0.b = 1w1;
-        }
-        {
-            tmp.a = s_0.b;
-            tmp.b = s_0.a;
-        }
-        {
-            s_0.a = tmp.a;
-            s_0.b = tmp.b;
-        }
-        b = s_0.a;
+        b = 1w1;
     }
 }
 control e<T>(out T t);
