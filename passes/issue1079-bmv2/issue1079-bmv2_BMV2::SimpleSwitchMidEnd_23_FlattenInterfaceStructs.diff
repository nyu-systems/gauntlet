--- before_pass
+++ after_pass
@@ -9,8 +9,8 @@ struct cksum_t {
     bit<16> result;
 }
 struct metadata_t {
-    cksum_t cksum;
-    bit<1>  b;
+    bit<16> _cksum_result0;
+    bit<1>  _b1;
 }
 parser EmptyParser(packet_in b, out headers_t headers, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
     state start {
@@ -22,7 +22,7 @@ struct tuple_0 {
 }
 control EmptyVerifyChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        verify_checksum<tuple_0, bit<16>>(false, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(false, { 16w0 }, meta._cksum_result0, HashAlgorithm.csum16);
     }
 }
 control EmptyIngress(inout headers_t headers, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
@@ -36,9 +36,9 @@ control EmptyEgress(inout headers_t hdr,
 }
 control EmptyComputeChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        update_checksum<tuple_0, bit<16>>(false, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
-        update_checksum<tuple_0, bit<16>>(hdr.e.isValid(), { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
-        update_checksum<tuple_0, bit<16>>(meta.b == 1w0, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(false, { 16w0 }, meta._cksum_result0, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(hdr.e.isValid(), { 16w0 }, meta._cksum_result0, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(meta._b1 == 1w0, { 16w0 }, meta._cksum_result0, HashAlgorithm.csum16);
     }
 }
 control EmptyDeparser(packet_out b, in headers_t hdr) {
