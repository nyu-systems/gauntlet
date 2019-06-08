--- before_pass
+++ after_pass
@@ -15,7 +15,20 @@ control c(inout bit<1> r) {
     S s_0;
     bit<1> tmp;
     apply {
-        s_0 = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
+        {
+            {
+                {
+                    s_0.f1.field.f = 1w0;
+                }
+                {
+                    s_0.f1.field_0.f = 1w1;
+                }
+            }
+            {
+                s_0.f2.f = 1w0;
+            }
+            s_0.z = 1w1;
+        }
         f<tuple_0>(s_0.f1);
         tmp = s_0.f2.f & s_0.z;
         r = tmp;
