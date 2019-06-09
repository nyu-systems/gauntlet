--- before_pass
+++ after_pass
@@ -44,11 +44,16 @@ parser parserI(packet_in pkt, out header
         transition accept;
     }
 }
+struct tuple_0 {
+    bit<32> field;
+    bit<32> field_0;
+    bit<8>  field_1;
+}
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     @name(".NoAction") action NoAction_0() {
     }
     @name("cIngress.hash_drop_decision") action hash_drop_decision() {
-        hash<bit<16>, bit<16>, tuple<bit<32>, bit<32>, bit<8>>, bit<32>>(meta.mystruct1.hash1, HashAlgorithm.crc16, 16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol }, 32w0xffff);
+        hash<bit<16>, bit<16>, tuple_0, bit<32>>(meta.mystruct1.hash1, HashAlgorithm.crc16, 16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol }, 32w0xffff);
         meta.mystruct1.hash_drop = meta.mystruct1.hash1 < 16w0x8000;
     }
     @name("cIngress.guh") table guh_0 {
