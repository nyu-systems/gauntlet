--- before_pass
+++ after_pass
@@ -224,14 +224,42 @@ control DeparserImpl(packet_out packet,
         packet.emit<custom_t>(hdr.custom);
     }
 }
+struct tuple_0 {
+    bit<48> field;
+    bit<48> field_0;
+    bit<48> field_1;
+    bit<8>  field_2;
+    bit<8>  field_3;
+    bit<8>  field_4;
+    bit<8>  field_5;
+    bit<8>  field_6;
+    bit<8>  field_7;
+    bit<8>  field_8;
+    bit<8>  field_9;
+    bit<8>  field_10;
+    bit<8>  field_11;
+    bit<8>  field_12;
+    bit<8>  field_13;
+    bit<8>  field_14;
+    bit<8>  field_15;
+    bit<8>  field_16;
+    bit<8>  field_17;
+    bit<8>  field_18;
+    bit<8>  field_19;
+    bit<8>  field_20;
+    bit<8>  field_21;
+    bit<8>  field_22;
+    bit<8>  field_23;
+    bit<8>  field_24;
+}
 control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        verify_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, bit<8>>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
     }
 }
 control computeChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        update_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, bit<8>>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
     }
 }
 V1Switch<headers_t, metadata_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
