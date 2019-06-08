--- before_pass
+++ after_pass
@@ -3,17 +3,12 @@ struct S {
     bit<1> b;
 }
 control c(out bit<1> b) {
-    S s;
     apply {
         {
-            s.a = 1w0;
-            s.b = 1w1;
         }
         {
-            s.a = s.b;
-            s.b = s.a;
         }
-        b = s.a;
+        b = 1w1;
     }
 }
 control e<T>(out T t);
