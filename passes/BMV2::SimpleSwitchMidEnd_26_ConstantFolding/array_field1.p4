--- dumps/p4_16_samples/array_field1.p4/pruned/array_field1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:09.832279600 +0200
+++ dumps/p4_16_samples/array_field1.p4/pruned/array_field1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:09.835245500 +0200
@@ -12,7 +12,7 @@ control my(out H[2] s) {
     bit<1> tmp_17;
     @name("my.act") action act_0() {
         s[32w0].z = 1w1;
-        s[32w0 + 32w1].z = 1w0;
+        s[32w1].z = 1w0;
         tmp_12 = 32w0;
         tmp_13 = s[32w0].z;
         tmp_17 = f(tmp_13, 1w0);
