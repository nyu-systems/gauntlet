--- dumps/p4_16_samples/issue1049-bmv2.p4/pruned/issue1049-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:31:10.341092300 +0200
+++ dumps/p4_16_samples/issue1049-bmv2.p4/pruned/issue1049-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:31:10.346760700 +0200
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
     @name("cIngress.hash_drop_decision") action hash_drop_decision_0() {
-        hash<bit<16>, bit<16>, tuple<bit<32>, bit<32>, bit<8>>, bit<32>>(meta.mystruct1.hash1, HashAlgorithm.crc16, 16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol }, 32w0xffff);
+        hash<bit<16>, bit<16>, tuple_0, bit<32>>(meta.mystruct1.hash1, HashAlgorithm.crc16, 16w0, { hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.protocol }, 32w0xffff);
         meta.mystruct1.hash_drop = meta.mystruct1.hash1 < 16w0x8000;
     }
     @name("cIngress.guh") table guh {
