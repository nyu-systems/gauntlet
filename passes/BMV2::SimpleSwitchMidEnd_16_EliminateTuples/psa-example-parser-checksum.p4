--- dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:34:10.539475100 +0200
+++ dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:34:10.541704800 +0200
@@ -51,6 +51,19 @@ struct headers {
 }
 typedef bit<32> PacketCounter_t;
 typedef bit<8> ErrorIndex_t;
+struct tuple_0 {
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
 parser IngressParserImpl(packet_in buffer, out headers hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
     bit<16> tmp_3;
     bool tmp_4;
@@ -67,7 +80,7 @@ parser IngressParserImpl(packet_in buffe
         buffer.extract<ipv4_t>(hdr.ipv4);
         verify(hdr.ipv4.ihl == 4w5, error.UnhandledIPv4Options);
         ck.clear();
-        ck.add<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>>({ hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr });
+        ck.add<tuple_0>({ hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr });
         tmp_3 = ck.get();
         tmp_4 = tmp_3 == hdr.ipv4.hdrChecksum;
         tmp_5 = tmp_4;
@@ -142,7 +155,7 @@ control EgressDeparserImpl(packet_out pa
     @name("EgressDeparserImpl.ck") InternetChecksum() ck_2;
     apply {
         ck_2.clear();
-        ck_2.add<tuple<bit<4>, bit<4>, bit<8>, bit<16>, bit<16>, bit<3>, bit<13>, bit<8>, bit<8>, bit<32>, bit<32>>>({ hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr });
+        ck_2.add<tuple_0>({ hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr });
         tmp_6 = ck_2.get();
         hdr.ipv4.hdrChecksum = tmp_6;
         packet.emit<ethernet_t>(hdr.ethernet);
