--- before_pass
+++ after_pass
@@ -12,25 +12,28 @@ struct S {
 }
 extern void f<D>(in D data);
 control c(inout bit<1> r) {
-    S s;
+    T s_f1_field;
+    T s_f1_field_0;
+    T s_f2;
+    bit<1> s_z;
     bit<1> tmp_0;
     apply {
         {
             {
                 {
-                    s.f1.field.f = 1w0;
+                    s_f1_field.f = 1w0;
                 }
                 {
-                    s.f1.field_0.f = 1w1;
+                    s_f1_field_0.f = 1w1;
                 }
             }
             {
-                s.f2.f = 1w0;
+                s_f2.f = 1w0;
             }
-            s.z = 1w1;
+            s_z = 1w1;
         }
-        f<tuple_0>(s.f1);
-        tmp_0 = s.f2.f & s.z;
+        f<tuple_0>({ s_f1_field, s_f1_field_0 });
+        tmp_0 = s_f2.f & s_z;
         r = tmp_0;
     }
 }
