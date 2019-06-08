--- dumps/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:59.795976500 +0200
+++ dumps/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:59.841433100 +0200
@@ -20,19 +20,9 @@ control c(inout bit<1> r) {
     T s_f1_field_0;
     T s_f2;
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
-            {
-                s_f2.f = 1w0;
-            }
-        }
+        s_f1_field.f = 1w0;
+        s_f1_field_0.f = 1w1;
+        s_f2.f = 1w0;
         f<tuple_1>({ s_f1_field, s_f1_field_0 });
         f<tuple_0>({ { 1w0 }, { 1w1 } });
         r = s_f2.f & 1w1;
