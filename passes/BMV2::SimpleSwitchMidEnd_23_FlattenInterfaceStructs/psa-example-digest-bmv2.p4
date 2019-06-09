--- before_pass
+++ after_pass
@@ -32,8 +32,9 @@ struct mac_learn_digest_t {
     PortId_t        ingress_port;
 }
 struct metadata {
-    bool               send_mac_learn_msg;
-    mac_learn_digest_t mac_learn_msg;
+    bool    _send_mac_learn_msg0;
+    bit<48> _mac_learn_msg_srcAddr1;
+    bit<32> _mac_learn_msg_ingress_port2;
 }
 parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
     state start {
@@ -83,9 +84,9 @@ control ingress(inout headers hdr, inout
     @name(".NoAction") action NoAction_5() {
     }
     @name("ingress.unknown_source") action unknown_source() {
-        meta.send_mac_learn_msg = true;
-        meta.mac_learn_msg.srcAddr = hdr.ethernet.srcAddr;
-        meta.mac_learn_msg.ingress_port = istd.ingress_port;
+        meta._send_mac_learn_msg0 = true;
+        meta._mac_learn_msg_srcAddr1 = hdr.ethernet.srcAddr;
+        meta._mac_learn_msg_ingress_port2 = istd.ingress_port;
     }
     @name("ingress.learned_sources") table learned_sources_0 {
         key = {
@@ -161,7 +162,7 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.tst_tbl") table tst_tbl_0 {
         key = {
-            meta.mac_learn_msg.ingress_port: exact @name("meta.mac_learn_msg.ingress_port") ;
+            meta._mac_learn_msg_ingress_port2: exact @name("meta.mac_learn_msg.ingress_port") ;
         }
         actions = {
             do_tst();
@@ -170,7 +171,7 @@ control ingress(inout headers hdr, inout
         default_action = NoAction_5();
     }
     apply {
-        meta.send_mac_learn_msg = false;
+        meta._send_mac_learn_msg0 = false;
         learned_sources_0.apply();
         l2_tbl_0.apply();
         tst_tbl_0.apply();
@@ -183,8 +184,8 @@ control egress(inout headers hdr, inout
 control IngressDeparserImpl(packet_out packet, out empty_metadata_t clone_i2e_meta, out empty_metadata_t resubmit_meta, out empty_metadata_t normal_meta, inout headers hdr, in metadata meta, in psa_ingress_output_metadata_t istd) {
     @name("IngressDeparserImpl.mac_learn_digest") Digest<mac_learn_digest_t>() mac_learn_digest_0;
     apply {
-        if (meta.send_mac_learn_msg) 
-            mac_learn_digest_0.pack(meta.mac_learn_msg);
+        if (meta._send_mac_learn_msg0) 
+            mac_learn_digest_0.pack({meta._mac_learn_msg_srcAddr1,meta._mac_learn_msg_ingress_port2});
         packet.emit<ethernet_t>(hdr.ethernet);
         packet.emit<ipv4_t>(hdr.ipv4);
     }
