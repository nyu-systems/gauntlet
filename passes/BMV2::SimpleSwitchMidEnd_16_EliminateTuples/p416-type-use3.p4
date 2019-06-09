--- before_pass
+++ after_pass
@@ -119,14 +119,31 @@ control DeparserImpl(packet_out packet,
         packet.emit<custom_t>(hdr.custom);
     }
 }
+struct tuple_0 {
+    bit<8> field;
+    bit<8> field_0;
+    bit<8> field_1;
+    bit<8> field_2;
+    bit<8> field_3;
+    bit<8> field_4;
+    bit<8> field_5;
+    bit<8> field_6;
+    bit<8> field_7;
+    bit<8> field_8;
+    bit<8> field_9;
+    bit<8> field_10;
+    bit<8> field_11;
+    bit<8> field_12;
+    bit<8> field_13;
+}
 control verifyChecksum(inout headers_t hdr, inout meta_t meta) {
     apply {
-        verify_checksum<tuple<bit<8>, bit<8>, CustomT_t, bit<8>, CustomDT_t, CustomT_t, CustomTT_t, bit<8>, CustomDDT_t, CustomDT_t, CustomDTT_t, CustomT_t, CustomTDT_t, CustomTT_t, CustomTTT_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.e, hdr.custom.ed, hdr.custom.et, hdr.custom.edd, hdr.custom.edt, hdr.custom.etd, hdr.custom.ett, hdr.custom.eddd, hdr.custom.eddt, hdr.custom.edtd, hdr.custom.edtt, hdr.custom.etdd, hdr.custom.etdt, hdr.custom.ettd, hdr.custom.ettt }, hdr.custom.checksum, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom.e, hdr.custom.ed, hdr.custom.et, hdr.custom.edd, hdr.custom.edt, hdr.custom.etd, hdr.custom.ett, hdr.custom.eddd, hdr.custom.eddt, hdr.custom.edtd, hdr.custom.edtt, hdr.custom.etdd, hdr.custom.etdt, hdr.custom.ettd, hdr.custom.ettt }, hdr.custom.checksum, HashAlgorithm.csum16);
     }
 }
 control computeChecksum(inout headers_t hdr, inout meta_t meta) {
     apply {
-        update_checksum<tuple<bit<8>, bit<8>, CustomT_t, bit<8>, CustomDT_t, CustomT_t, CustomTT_t, bit<8>, CustomDDT_t, CustomDT_t, CustomDTT_t, CustomT_t, CustomTDT_t, CustomTT_t, CustomTTT_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.e, hdr.custom.ed, hdr.custom.et, hdr.custom.edd, hdr.custom.edt, hdr.custom.etd, hdr.custom.ett, hdr.custom.eddd, hdr.custom.eddt, hdr.custom.edtd, hdr.custom.edtt, hdr.custom.etdd, hdr.custom.etdt, hdr.custom.ettd, hdr.custom.ettt }, hdr.custom.checksum, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom.e, hdr.custom.ed, hdr.custom.et, hdr.custom.edd, hdr.custom.edt, hdr.custom.etd, hdr.custom.ett, hdr.custom.eddd, hdr.custom.eddt, hdr.custom.edtd, hdr.custom.edtt, hdr.custom.etdd, hdr.custom.etdt, hdr.custom.ettd, hdr.custom.ettt }, hdr.custom.checksum, HashAlgorithm.csum16);
     }
 }
 V1Switch<headers_t, meta_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
