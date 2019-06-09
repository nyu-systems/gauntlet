--- before_pass
+++ after_pass
@@ -74,7 +74,7 @@ parser MyParser(packet_in packet, out he
                 tmp_1.res = tmp_5[31:0];
             }
         }
-        transition select(tmp.p, tmp_0.four, tmp_1.ver) {
+        transition select(tmp_3[127:120], tmp_4[119:112], tmp_5[111:104]) {
             (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
             default: accept;
         }
@@ -93,10 +93,7 @@ struct tuple_0 {
 }
 control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     bit<48> tmp_2;
-    bit<32> nbase_0;
-    bit<64> ncount_0;
     bit<32> nselect_0;
-    bit<32> ninput_0;
     @name("MyIngress.operation_add") action operation_add() {
         hdr.p4calc.res = hdr.p4calc.operand_a + hdr.p4calc.operand_b;
         tmp_2 = hdr.ethernet.dstAddr;
@@ -133,10 +130,7 @@ control MyIngress(inout headers hdr, ino
         standard_metadata.egress_spec = standard_metadata.ingress_port;
     }
     @name("MyIngress.operation_crc") action operation_crc() {
-        nbase_0 = hdr.p4calc.operand_b;
-        ncount_0 = 64w8589934592;
-        ninput_0 = hdr.p4calc.operand_a;
-        hash<bit<32>, bit<32>, tuple_0, bit<64>>(nselect_0, HashAlgorithm.crc32, nbase_0, { ninput_0 }, ncount_0);
+        hash<bit<32>, bit<32>, tuple_0, bit<64>>(nselect_0, HashAlgorithm.crc32, hdr.p4calc.operand_b, { hdr.p4calc.operand_a }, 64w8589934592);
         hdr.p4calc.res = nselect_0;
         tmp_2 = hdr.ethernet.dstAddr;
         hdr.ethernet.dstAddr = hdr.ethernet.srcAddr;
