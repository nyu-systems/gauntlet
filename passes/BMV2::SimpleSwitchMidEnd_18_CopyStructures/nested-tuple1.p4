--- before_pass
+++ after_pass
@@ -15,7 +15,20 @@ control c(inout bit<1> r) {
     S s;
     bit<1> tmp_0;
     apply {
-        s = S {f1 = { T {f = 1w0}, T {f = 1w1} },f2 = T {f = 1w0},z = 1w1};
+        {
+            {
+                {
+                    s.f1.field.f = 1w0;
+                }
+                {
+                    s.f1.field_0.f = 1w1;
+                }
+            }
+            {
+                s.f2.f = 1w0;
+            }
+            s.z = 1w1;
+        }
         f<tuple_0>(s.f1);
         tmp_0 = s.f2.f & s.z;
         r = tmp_0;
