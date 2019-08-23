--- before_pass
+++ after_pass
@@ -155,9 +155,16 @@ control MyVerifyChecksum(inout headers h
     apply {
     }
 }
+struct tuple_0 {
+    bit<128> field;
+    bit<128> field_0;
+    bit<32>  field_1;
+    bit<24>  field_2;
+    bit<8>   field_3;
+}
 control MyComputeChecksum(inout headers hdr, inout metadata meta) {
     apply {
-        update_checksum_with_payload<tuple<bit<128>, bit<128>, bit<32>, bit<24>, bit<8>>, bit<16>>(meta.do_cksum == 1w1, { hdr.ipv6.src_addr, hdr.ipv6.dst_addr, (bit<32>)hdr.ipv6.payload_length, 24w0, 8w58 }, hdr.icmp6.checksum, HashAlgorithm.csum16);
+        update_checksum_with_payload<tuple_0, bit<16>>(meta.do_cksum == 1w1, { hdr.ipv6.src_addr, hdr.ipv6.dst_addr, (bit<32>)hdr.ipv6.payload_length, 24w0, 8w58 }, hdr.icmp6.checksum, HashAlgorithm.csum16);
     }
 }
 control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
