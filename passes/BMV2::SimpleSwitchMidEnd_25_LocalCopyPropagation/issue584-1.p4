--- dumps/pruned/issue584-1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:37.309814100 +0200
+++ dumps/pruned/issue584-1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:37.312031500 +0200
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
