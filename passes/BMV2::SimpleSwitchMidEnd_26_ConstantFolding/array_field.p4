--- dumps/p4_16_samples/array_field.p4/pruned/array_field-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:09.465551900 +0200
+++ dumps/p4_16_samples/array_field.p4/pruned/array_field-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:09.467909100 +0200
@@ -8,7 +8,7 @@ control my(out H[2] s) {
     bit<32> tmp_1;
     apply {
         s[32w0].z = 1w1;
-        s[32w0 + 32w1].z = 1w0;
+        s[32w1].z = 1w0;
         tmp_1 = f(s[32w0].z, 1w0);
         f(s[tmp_1].z, 1w1);
     }
