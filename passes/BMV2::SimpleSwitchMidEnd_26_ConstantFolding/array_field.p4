--- dumps/pruned/array_field-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:08.640800300 +0200
+++ dumps/pruned/array_field-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:08.643693000 +0200
@@ -8,7 +8,7 @@ control my(out H[2] s) {
     bit<32> tmp_1;
     apply {
         s[32w0].z = 1w1;
-        s[32w0 + 32w1].z = 1w0;
+        s[32w1].z = 1w0;
         tmp_1 = f(s[32w0].z, 1w0);
         f(s[tmp_1].z, 1w1);
     }
