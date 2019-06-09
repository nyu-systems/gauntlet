--- before_pass
+++ after_pass
@@ -4,9 +4,20 @@ struct S {
 }
 control c(out bit<1> b) {
     S s_0;
+    S tmp;
     apply {
-        s_0 = { 1w0, 1w1 };
-        s_0 = {s_0.b,s_0.a};
+        {
+            s_0.a = 1w0;
+            s_0.b = 1w1;
+        }
+        {
+            tmp.a = s_0.b;
+            tmp.b = s_0.a;
+        }
+        {
+            s_0.a = tmp.a;
+            s_0.b = tmp.b;
+        }
         b = s_0.a;
     }
 }
