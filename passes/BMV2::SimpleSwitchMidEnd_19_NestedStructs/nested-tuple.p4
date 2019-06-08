--- before_pass
+++ after_pass
@@ -16,25 +16,28 @@ struct tuple_0 {
 }
 extern void f<T>(in T data);
 control c(inout bit<1> r) {
-    S s;
+    T s_f1_field;
+    T s_f1_field_0;
+    T s_f2;
+    bit<1> s_z;
     apply {
         {
             {
                 {
-                    s.f1.field_1.f = 1w0;
+                    s_f1_field.f = 1w0;
                 }
                 {
-                    s.f1.field_2.f = 1w1;
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
-        f<tuple_1>(s.f1);
+        f<tuple_1>({ s_f1_field, s_f1_field_0 });
         f<tuple_0>({ { 1w0 }, { 1w1 } });
-        r = s.f2.f & s.z;
+        r = s_f2.f & s_z;
     }
 }
 control simple(inout bit<1> r);
