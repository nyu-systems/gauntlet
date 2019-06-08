--- before_pass
+++ after_pass
@@ -41,7 +41,13 @@ parser IngressParserImpl(packet_in buffe
     state start {
         parsed_hdr_2.ethernet.setInvalid();
         parsed_hdr_2.ipv4.setInvalid();
-        meta_0 = meta;
+        {
+            meta_0.send_mac_learn_msg = meta.send_mac_learn_msg;
+            {
+                meta_0.mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
+                meta_0.mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
+            }
+        }
         buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
         transition select(parsed_hdr_2.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -53,8 +59,18 @@ parser IngressParserImpl(packet_in buffe
         transition start_0;
     }
     state start_0 {
-        parsed_hdr = parsed_hdr_2;
-        meta = meta_0;
+        {
+            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
+            parsed_hdr.type = parsed_hdr_2.type;
+        }
+        {
+            meta.send_mac_learn_msg = meta_0.send_mac_learn_msg;
+            {
+                meta.mac_learn_msg.srcAddr = meta_0.mac_learn_msg.srcAddr;
+                meta.mac_learn_msg.ingress_port = meta_0.mac_learn_msg.ingress_port;
+            }
+        }
         transition accept;
     }
 }
@@ -64,7 +80,13 @@ parser EgressParserImpl(packet_in buffer
     state start {
         parsed_hdr_3.ethernet.setInvalid();
         parsed_hdr_3.ipv4.setInvalid();
-        meta_5 = meta;
+        {
+            meta_5.send_mac_learn_msg = meta.send_mac_learn_msg;
+            {
+                meta_5.mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
+                meta_5.mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
+            }
+        }
         buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
         transition select(parsed_hdr_3.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
@@ -76,8 +98,18 @@ parser EgressParserImpl(packet_in buffer
         transition start_1;
     }
     state start_1 {
-        parsed_hdr = parsed_hdr_3;
-        meta = meta_5;
+        {
+            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
+            parsed_hdr.type = parsed_hdr_3.type;
+        }
+        {
+            meta.send_mac_learn_msg = meta_5.send_mac_learn_msg;
+            {
+                meta.mac_learn_msg.srcAddr = meta_5.mac_learn_msg.srcAddr;
+                meta.mac_learn_msg.ingress_port = meta_5.mac_learn_msg.ingress_port;
+            }
+        }
         transition accept;
     }
 }
@@ -109,22 +141,54 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
         {
-            meta_6 = ostd;
+            {
+                meta_6.class_of_service = ostd.class_of_service;
+                meta_6.clone = ostd.clone;
+                meta_6.clone_session_id = ostd.clone_session_id;
+                meta_6.drop = ostd.drop;
+                meta_6.resubmit = ostd.resubmit;
+                meta_6.multicast_group = ostd.multicast_group;
+                meta_6.egress_port = ostd.egress_port;
+            }
             egress_port_0 = egress_port;
             meta_6.drop = false;
             meta_6.multicast_group = 10w0;
             meta_6.egress_port = egress_port_0;
-            ostd = meta_6;
+            {
+                ostd.class_of_service = meta_6.class_of_service;
+                ostd.clone = meta_6.clone;
+                ostd.clone_session_id = meta_6.clone_session_id;
+                ostd.drop = meta_6.drop;
+                ostd.resubmit = meta_6.resubmit;
+                ostd.multicast_group = meta_6.multicast_group;
+                ostd.egress_port = meta_6.egress_port;
+            }
         }
     }
     @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
         {
-            meta_7 = ostd;
+            {
+                meta_7.class_of_service = ostd.class_of_service;
+                meta_7.clone = ostd.clone;
+                meta_7.clone_session_id = ostd.clone_session_id;
+                meta_7.drop = ostd.drop;
+                meta_7.resubmit = ostd.resubmit;
+                meta_7.multicast_group = ostd.multicast_group;
+                meta_7.egress_port = ostd.egress_port;
+            }
             egress_port_3 = egress_port;
             meta_7.drop = false;
             meta_7.multicast_group = 10w0;
             meta_7.egress_port = egress_port_3;
-            ostd = meta_7;
+            {
+                ostd.class_of_service = meta_7.class_of_service;
+                ostd.clone = meta_7.clone;
+                ostd.clone_session_id = meta_7.clone_session_id;
+                ostd.drop = meta_7.drop;
+                ostd.resubmit = meta_7.resubmit;
+                ostd.multicast_group = meta_7.multicast_group;
+                ostd.egress_port = meta_7.egress_port;
+            }
         }
     }
     @name("ingress.l2_tbl") table l2_tbl {
