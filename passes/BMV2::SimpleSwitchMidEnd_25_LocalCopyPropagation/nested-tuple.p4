--- dumps/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:59.786797800 +0200
+++ dumps/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:59.789124700 +0200
@@ -19,7 +19,6 @@ control c(inout bit<1> r) {
     T s_f1_field;
     T s_f1_field_0;
     T s_f2;
-    bit<1> s_z;
     apply {
         {
             {
@@ -33,11 +32,10 @@ control c(inout bit<1> r) {
             {
                 s_f2.f = 1w0;
             }
-            s_z = 1w1;
         }
         f<tuple_1>({ s_f1_field, s_f1_field_0 });
         f<tuple_0>({ { 1w0 }, { 1w1 } });
-        r = s_f2.f & s_z;
+        r = s_f2.f & 1w1;
     }
 }
 control simple(inout bit<1> r);
