--- dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:26.472907700 +0200
+++ dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:26.476183800 +0200
@@ -15,8 +15,6 @@ control c(inout bit<1> r) {
     T s_0_f1_field;
     T s_0_f1_field_0;
     T s_0_f2;
-    bit<1> s_0_z;
-    bit<1> tmp;
     apply {
         {
             {
@@ -30,11 +28,9 @@ control c(inout bit<1> r) {
             {
                 s_0_f2.f = 1w0;
             }
-            s_0_z = 1w1;
         }
         f<tuple_0>({ s_0_f1_field, s_0_f1_field_0 });
-        tmp = s_0_f2.f & s_0_z;
-        r = tmp;
+        r = s_0_f2.f & 1w1;
     }
 }
 control simple(inout bit<1> r);
