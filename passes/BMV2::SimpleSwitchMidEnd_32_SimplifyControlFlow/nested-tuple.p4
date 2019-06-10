--- before_pass
+++ after_pass
@@ -19,16 +19,8 @@ control c(inout bit<1> r) {
     T s_0_f1_field;
     T s_0_f1_field_0;
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
-        }
+        s_0_f1_field.f = 1w0;
+        s_0_f1_field_0.f = 1w1;
         f<tuple_1>({ s_0_f1_field, s_0_f1_field_0 });
         f<tuple_0>(tuple_0 {field = T {f = 1w0},field_0 = T {f = 1w1}});
         r = 1w0;
