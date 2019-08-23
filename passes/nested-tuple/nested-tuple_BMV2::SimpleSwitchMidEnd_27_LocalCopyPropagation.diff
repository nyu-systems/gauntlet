--- before_pass
+++ after_pass
@@ -18,8 +18,6 @@ extern void f<T>(in T data);
 control c(inout bit<1> r) {
     T s_0_f1_field;
     T s_0_f1_field_0;
-    T s_0_f2;
-    bit<1> s_0_z;
     apply {
         {
             {
@@ -30,14 +28,10 @@ control c(inout bit<1> r) {
                     s_0_f1_field_0.f = 1w1;
                 }
             }
-            {
-                s_0_f2.f = 1w0;
-            }
-            s_0_z = 1w1;
         }
         f<tuple_1>({ s_0_f1_field, s_0_f1_field_0 });
         f<tuple_0>(tuple_0 {field = T {f = 1w0},field_0 = T {f = 1w1}});
-        r = s_0_f2.f & s_0_z;
+        r = 1w0 & 1w1;
     }
 }
 control simple(inout bit<1> r);
