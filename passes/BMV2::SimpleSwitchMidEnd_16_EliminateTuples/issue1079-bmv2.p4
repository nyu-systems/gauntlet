--- before_pass
+++ after_pass
@@ -17,9 +17,12 @@ parser EmptyParser(packet_in b, out head
         transition accept;
     }
 }
+struct tuple_0 {
+    bit<16> field;
+}
 control EmptyVerifyChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        verify_checksum<tuple<bit<16>>, bit<16>>(false, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(false, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
     }
 }
 control EmptyIngress(inout headers_t headers, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
@@ -33,9 +36,9 @@ control EmptyEgress(inout headers_t hdr,
 }
 control EmptyComputeChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        update_checksum<tuple<bit<16>>, bit<16>>(false, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
-        update_checksum<tuple<bit<16>>, bit<16>>(hdr.e.isValid(), { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
-        update_checksum<tuple<bit<16>>, bit<16>>(meta.b == 1w0, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(false, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(hdr.e.isValid(), { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(meta.b == 1w0, { 16w0 }, meta.cksum.result, HashAlgorithm.csum16);
     }
 }
 control EmptyDeparser(packet_out b, in headers_t hdr) {
