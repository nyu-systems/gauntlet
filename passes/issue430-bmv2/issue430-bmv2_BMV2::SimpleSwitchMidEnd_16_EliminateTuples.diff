--- before_pass
+++ after_pass
@@ -17,10 +17,13 @@ control MyVerifyChecksum(inout my_packet
     apply {
     }
 }
+struct tuple_0 {
+    bit<32> field;
+}
 control MyIngress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
     bit<32> x_0;
     apply {
-        hash<bit<32>, bit<32>, tuple<bit<32>>, bit<32>>(x_0, HashAlgorithm.crc32, 32w0, { p.h.f ^ 32w0xffff }, 32w65536);
+        hash<bit<32>, bit<32>, tuple_0, bit<32>>(x_0, HashAlgorithm.crc32, 32w0, { p.h.f ^ 32w0xffff }, 32w65536);
     }
 }
 control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
