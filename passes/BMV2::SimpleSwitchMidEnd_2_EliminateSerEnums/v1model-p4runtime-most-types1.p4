--- before_pass
+++ after_pass
@@ -28,11 +28,7 @@ typedef Custom00200_t Custom002001_t;
 typedef Custom00200_t Custom002002_t;
 typedef Custom002001_t Custom0020010_t;
 typedef Custom002002_t Custom0020020_t;
-enum bit<8> serenum_t {
-    A = 8w1,
-    B = 8w3
-}
-typedef serenum_t serenum0_t;
+typedef bit<8> serenum0_t;
 header ethernet_t {
     Eth0_t  dstAddr;
     Eth1_t  srcAddr;
@@ -70,7 +66,7 @@ header custom_t {
     Custom0020020_t e0020020;
     struct1_t       my_nested_struct1;
     bit<16>         checksum;
-    serenum0_t      s0;
+    bit<8>          s0;
 }
 @controller_header("packet_in") header packet_in_header_t {
     bit<8> punt_reason;
@@ -147,7 +143,7 @@ control ingress(inout headers_t hdr, ino
     @name("ingress.set_output") action set_output(bit<9> out_port) {
         stdmeta.egress_spec = out_port;
     }
-    @name("ingress.set_headers") action set_headers(Eth0_t addr0, Eth1_t addr1, Eth2_t addr2, bit<8> e, Custom0_t e0, Custom1_t e1, Custom2_t e2, Custom00_t e00, Custom01_t e01, Custom02_t e02, Custom10_t e10, Custom11_t e11, Custom12_t e12, Custom20_t e20, Custom21_t e21, Custom22_t e22, Custom001_t e001, Custom002_t e002, Custom101_t e101, Custom102_t e102, Custom201_t e201, Custom202_t e202, Custom220_t e220, Custom0020010_t e0020010, Custom0020020_t e0020020, serenum0_t s0) {
+    @name("ingress.set_headers") action set_headers(Eth0_t addr0, Eth1_t addr1, Eth2_t addr2, bit<8> e, Custom0_t e0, Custom1_t e1, Custom2_t e2, Custom00_t e00, Custom01_t e01, Custom02_t e02, Custom10_t e10, Custom11_t e11, Custom12_t e12, Custom20_t e20, Custom21_t e21, Custom22_t e22, Custom001_t e001, Custom002_t e002, Custom101_t e101, Custom102_t e102, Custom201_t e201, Custom202_t e202, Custom220_t e220, Custom0020010_t e0020010, Custom0020020_t e0020020, bit<8> s0) {
         hdr.custom.addr0 = addr0;
         hdr.custom.addr1 = addr1;
         hdr.custom.addr2 = addr2;
@@ -230,12 +226,12 @@ control DeparserImpl(packet_out packet,
 }
 control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        verify_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, serenum_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
+        verify_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, bit<8>>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
     }
 }
 control computeChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        update_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, serenum_t>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
+        update_checksum<tuple<bit<48>, Eth1_t, Eth2_t, bit<8>, bit<8>, Custom1_t, Custom2_t, bit<8>, Custom01_t, Custom02_t, Custom1_t, Custom11_t, Custom12_t, Custom2_t, Custom21_t, Custom22_t, Custom001_t, Custom002_t, Custom101_t, Custom102_t, Custom201_t, Custom202_t, Custom22_t, Custom002001_t, Custom002002_t, bit<8>>, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
     }
 }
 V1Switch<headers_t, metadata_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
