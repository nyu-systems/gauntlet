--- before_pass
+++ after_pass
@@ -65,8 +65,6 @@ struct tuple_0 {
 }
 parser IngressParserImpl(packet_in buffer, out headers hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
     bit<16> tmp;
-    bool tmp_0;
-    bool tmp_1;
     @name("IngressParserImpl.ck") InternetChecksum() ck_0;
     state start {
         buffer.extract<ethernet_t>(hdr.ethernet);
@@ -81,9 +79,7 @@ parser IngressParserImpl(packet_in buffe
         ck_0.clear();
         ck_0.add<tuple_0>({ hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, hdr.ipv4.ttl, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr });
         tmp = ck_0.get();
-        tmp_0 = tmp == hdr.ipv4.hdrChecksum;
-        tmp_1 = tmp_0;
-        verify(tmp_1, error.BadIPv4HeaderChecksum);
+        verify(tmp == hdr.ipv4.hdrChecksum, error.BadIPv4HeaderChecksum);
         transition select(hdr.ipv4.protocol) {
             8w6: parse_tcp;
             default: accept;
@@ -95,26 +91,9 @@ parser IngressParserImpl(packet_in buffe
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    psa_ingress_output_metadata_t meta_1;
     @name(".ingress_drop") action ingress_drop() {
         {
-            meta_1.class_of_service = ostd.class_of_service;
-            meta_1.clone = ostd.clone;
-            meta_1.clone_session_id = ostd.clone_session_id;
-            meta_1.drop = ostd.drop;
-            meta_1.resubmit = ostd.resubmit;
-            meta_1.multicast_group = ostd.multicast_group;
-            meta_1.egress_port = ostd.egress_port;
-        }
-        meta_1.drop = true;
-        {
-            ostd.class_of_service = meta_1.class_of_service;
-            ostd.clone = meta_1.clone;
-            ostd.clone_session_id = meta_1.clone_session_id;
-            ostd.drop = meta_1.drop;
-            ostd.resubmit = meta_1.resubmit;
-            ostd.multicast_group = meta_1.multicast_group;
-            ostd.egress_port = meta_1.egress_port;
+            ostd.drop = true;
         }
     }
     @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts_0;
