--- before_pass
+++ after_pass
@@ -14,9 +14,6 @@ extern void f<D>(in D data);
 control c(inout bit<1> r) {
     T s_f1_field;
     T s_f1_field_0;
-    T s_f2;
-    bit<1> s_z;
-    bit<1> tmp_0;
     apply {
         {
             {
@@ -27,14 +24,9 @@ control c(inout bit<1> r) {
                     s_f1_field_0.f = 1w1;
                 }
             }
-            {
-                s_f2.f = 1w0;
-            }
-            s_z = 1w1;
         }
         f<tuple_0>({ s_f1_field, s_f1_field_0 });
-        tmp_0 = s_f2.f & s_z;
-        r = tmp_0;
+        r = 1w0 & 1w1;
     }
 }
 control simple(inout bit<1> r);
