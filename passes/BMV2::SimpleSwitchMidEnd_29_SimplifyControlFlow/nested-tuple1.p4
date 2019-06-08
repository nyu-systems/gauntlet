--- before_pass
+++ after_pass
@@ -16,19 +16,9 @@ control c(inout bit<1> r) {
     T s_0_f1_field_0;
     T s_0_f2;
     apply {
-        {
-            {
-                {
-                    s_0_f1_field.f = 1w0;
-                }
-                {
-                    s_0_f1_field_0.f = 1w1;
-                }
-            }
-            {
-                s_0_f2.f = 1w0;
-            }
-        }
+        s_0_f1_field.f = 1w0;
+        s_0_f1_field_0.f = 1w1;
+        s_0_f2.f = 1w0;
         f<tuple_0>({ s_0_f1_field, s_0_f1_field_0 });
         r = s_0_f2.f & 1w1;
     }
