--- before_pass
+++ after_pass
@@ -26,9 +26,12 @@ control ComputeChecksumI(inout H hdr, in
     apply {
     }
 }
+struct tuple_0 {
+    bit<32> field;
+}
 control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
     @name("IngressI.a") action a_0() {
-        hash<bit<16>, bit<16>, tuple<bit<32>>, bit<32>>(meta.hash.hash, HashAlgorithm.crc16, 16w0, { meta.ipv4.lkp_ipv4_sa }, 32w65536);
+        hash<bit<16>, bit<16>, tuple_0, bit<32>>(meta.hash.hash, HashAlgorithm.crc16, 16w0, { meta.ipv4.lkp_ipv4_sa }, 32w65536);
     }
     apply {
         a_0();
