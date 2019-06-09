--- before_pass
+++ after_pass
@@ -48,6 +48,8 @@ parser ParserImpl(packet_in packet, out
         transition accept;
     }
 }
+struct tuple_0 {
+}
 control ingress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
     bit<32> ipv4_address_0;
     bit<8> byte0_0;
@@ -74,10 +76,10 @@ control ingress(inout headers_t hdr, ino
     }
     @name("ingress.do_resubmit") action do_resubmit(bit<32> new_ipv4_dstAddr) {
         hdr.ipv4.dstAddr = new_ipv4_dstAddr;
-        resubmit<tuple<>>({  });
+        resubmit<tuple_0>({  });
     }
     @name("ingress.do_clone_i2e") action do_clone_i2e(bit<32> l2ptr) {
-        clone3<tuple<>>(CloneType.I2E, 32w5, {  });
+        clone3<tuple_0>(CloneType.I2E, 32w5, {  });
         meta.fwd.l2ptr = l2ptr;
     }
     @name("ingress.ipv4_da_lpm") table ipv4_da_lpm_0 {
@@ -163,11 +165,11 @@ control egress(inout headers_t hdr, inou
     }
     @name("egress.do_recirculate") action do_recirculate(bit<32> new_ipv4_dstAddr) {
         hdr.ipv4.dstAddr = new_ipv4_dstAddr;
-        recirculate<tuple<>>({  });
+        recirculate<tuple_0>({  });
     }
     @name("egress.do_clone_e2e") action do_clone_e2e(bit<48> smac) {
         hdr.ethernet.srcAddr = smac;
-        clone3<tuple<>>(CloneType.E2E, 32w11, {  });
+        clone3<tuple_0>(CloneType.E2E, 32w11, {  });
     }
     @name("egress.send_frame") table send_frame_0 {
         key = {
@@ -207,14 +209,27 @@ control DeparserImpl(packet_out packet,
         packet.emit<ipv4_t>(hdr.ipv4);
     }
 }
+struct tuple_1 {
+    bit<4>  field;
+    bit<4>  field_0;
+    bit<8>  field_1;
+    bit<16> field_2;
+    bit<16> field_3;
+    bit<3>  field_4;
+    bit<13> field_5;
+    bit<8>  field_6;
+    bit<8>  field_7;
+    bit<32> field_8;
+    bit<32> field_9;
+}
 control verifyChecksum(inout headers_t hdr, inout meta_t meta) {
     apply {
-        verify_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.isValid() && hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
+        verify_checksum<tuple_1, bit<16>>(hdr.ipv4.isValid() && hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
     }
 }
 control computeChecksum(inout headers_t hdr, inout meta_t meta) {
     apply {
-        update_checksum<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>, bit<16>>(hdr.ipv4.isValid() && hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
+        update_checksum<tuple_1, bit<16>>(hdr.ipv4.isValid() && hdr.ipv4.ihl == 4w5, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
     }
 }
 V1Switch<headers_t, meta_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
