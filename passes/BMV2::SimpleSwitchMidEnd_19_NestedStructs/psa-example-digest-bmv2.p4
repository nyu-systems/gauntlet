--- before_pass
+++ after_pass
@@ -36,78 +36,84 @@ struct metadata {
     mac_learn_digest_t mac_learn_msg;
 }
 parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
-    headers parsed_hdr_2;
-    metadata meta_0;
+    ethernet_t parsed_hdr_2_ethernet;
+    ipv4_t parsed_hdr_2_ipv4;
+    bit<16> parsed_hdr_2_type;
+    bool meta_0_send_mac_learn_msg;
+    mac_learn_digest_t meta_0_mac_learn_msg;
     state start {
-        parsed_hdr_2.ethernet.setInvalid();
-        parsed_hdr_2.ipv4.setInvalid();
+        parsed_hdr_2_ethernet.setInvalid();
+        parsed_hdr_2_ipv4.setInvalid();
         {
-            meta_0.send_mac_learn_msg = meta.send_mac_learn_msg;
+            meta_0_send_mac_learn_msg = meta.send_mac_learn_msg;
             {
-                meta_0.mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
-                meta_0.mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
+                meta_0_mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
+                meta_0_mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
             }
         }
-        buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
-        transition select(parsed_hdr_2.ethernet.etherType) {
+        buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
+        transition select(parsed_hdr_2_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
             default: start_0;
         }
     }
     state CommonParser_parse_ipv4 {
-        buffer.extract<ipv4_t>(parsed_hdr_2.ipv4);
+        buffer.extract<ipv4_t>(parsed_hdr_2_ipv4);
         transition start_0;
     }
     state start_0 {
         {
-            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
-            parsed_hdr.type = parsed_hdr_2.type;
+            parsed_hdr.ethernet = parsed_hdr_2_ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
+            parsed_hdr.type = parsed_hdr_2_type;
         }
         {
-            meta.send_mac_learn_msg = meta_0.send_mac_learn_msg;
+            meta.send_mac_learn_msg = meta_0_send_mac_learn_msg;
             {
-                meta.mac_learn_msg.srcAddr = meta_0.mac_learn_msg.srcAddr;
-                meta.mac_learn_msg.ingress_port = meta_0.mac_learn_msg.ingress_port;
+                meta.mac_learn_msg.srcAddr = meta_0_mac_learn_msg.srcAddr;
+                meta.mac_learn_msg.ingress_port = meta_0_mac_learn_msg.ingress_port;
             }
         }
         transition accept;
     }
 }
 parser EgressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
-    headers parsed_hdr_3;
-    metadata meta_5;
+    ethernet_t parsed_hdr_3_ethernet;
+    ipv4_t parsed_hdr_3_ipv4;
+    bit<16> parsed_hdr_3_type;
+    bool meta_5_send_mac_learn_msg;
+    mac_learn_digest_t meta_5_mac_learn_msg;
     state start {
-        parsed_hdr_3.ethernet.setInvalid();
-        parsed_hdr_3.ipv4.setInvalid();
+        parsed_hdr_3_ethernet.setInvalid();
+        parsed_hdr_3_ipv4.setInvalid();
         {
-            meta_5.send_mac_learn_msg = meta.send_mac_learn_msg;
+            meta_5_send_mac_learn_msg = meta.send_mac_learn_msg;
             {
-                meta_5.mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
-                meta_5.mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
+                meta_5_mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
+                meta_5_mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
             }
         }
-        buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
-        transition select(parsed_hdr_3.ethernet.etherType) {
+        buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
+        transition select(parsed_hdr_3_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
             default: start_1;
         }
     }
     state CommonParser_parse_ipv4_0 {
-        buffer.extract<ipv4_t>(parsed_hdr_3.ipv4);
+        buffer.extract<ipv4_t>(parsed_hdr_3_ipv4);
         transition start_1;
     }
     state start_1 {
         {
-            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
-            parsed_hdr.type = parsed_hdr_3.type;
+            parsed_hdr.ethernet = parsed_hdr_3_ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
+            parsed_hdr.type = parsed_hdr_3_type;
         }
         {
-            meta.send_mac_learn_msg = meta_5.send_mac_learn_msg;
+            meta.send_mac_learn_msg = meta_5_send_mac_learn_msg;
             {
-                meta.mac_learn_msg.srcAddr = meta_5.mac_learn_msg.srcAddr;
-                meta.mac_learn_msg.ingress_port = meta_5.mac_learn_msg.ingress_port;
+                meta.mac_learn_msg.srcAddr = meta_5_mac_learn_msg.srcAddr;
+                meta.mac_learn_msg.ingress_port = meta_5_mac_learn_msg.ingress_port;
             }
         }
         transition accept;
