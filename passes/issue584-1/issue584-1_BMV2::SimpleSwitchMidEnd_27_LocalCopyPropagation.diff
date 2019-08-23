--- before_pass
+++ after_pass
@@ -4,10 +4,8 @@ control p();
 package top(p _p);
 control c() {
     bit<16> var_0;
-    bit<32> hdr_0;
     apply {
-        hdr_0 = 32w0;
-        hash<bit<16>, bit<16>, bit<32>, bit<16>>(var_0, HashAlgorithm.crc16, 16w0, hdr_0, 16w0xffff);
+        hash<bit<16>, bit<16>, bit<32>, bit<16>>(var_0, HashAlgorithm.crc16, 16w0, 32w0, 16w0xffff);
     }
 }
 top(c()) main;
