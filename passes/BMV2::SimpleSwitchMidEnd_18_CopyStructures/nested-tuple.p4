--- before_pass
+++ after_pass
@@ -18,7 +18,20 @@ extern void f<T>(in T data);
 control c(inout bit<1> r) {
     S s_0;
     apply {
-        s_0 = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
+        {
+            {
+                {
+                    s_0.f1.field_1.f = 1w0;
+                }
+                {
+                    s_0.f1.field_2.f = 1w1;
+                }
+            }
+            {
+                s_0.f2.f = 1w0;
+            }
+            s_0.z = 1w1;
+        }
         f<tuple_1>(s_0.f1);
         f<tuple_0>({{1w0},{1w1}});
         r = s_0.f2.f & s_0.z;
