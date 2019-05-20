--- dumps/p4_16_samples/issue584-1.p4/pruned/issue584-1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:58.787496500 +0200
+++ dumps/p4_16_samples/issue584-1.p4/pruned/issue584-1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:58.790033300 +0200
@@ -4,10 +4,8 @@ control p();
 package top(p _p);
 control c() {
     bit<16> var;
-    bit<32> hdr_1;
     apply {
-        hdr_1 = 32w0;
-        hash<bit<16>, bit<16>, bit<32>, bit<16>>(var, HashAlgorithm.crc16, 16w0, hdr_1, 16w0xffff);
+        hash<bit<16>, bit<16>, bit<32>, bit<16>>(var, HashAlgorithm.crc16, 16w0, 32w0, 16w0xffff);
     }
 }
 top(c()) main;
