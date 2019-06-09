--- before_pass
+++ after_pass
@@ -15,16 +15,8 @@ control c(inout bit<1> r) {
     T s_f1_field;
     T s_f1_field_0;
     apply {
-        {
-            {
-                {
-                    s_f1_field.f = 1w0;
-                }
-                {
-                    s_f1_field_0.f = 1w1;
-                }
-            }
-        }
+        s_f1_field.f = 1w0;
+        s_f1_field_0.f = 1w1;
         f<tuple_0>({ s_f1_field, s_f1_field_0 });
         r = 1w0;
     }
