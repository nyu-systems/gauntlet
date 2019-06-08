--- before_pass
+++ after_pass
@@ -39,7 +39,10 @@ parser IngressParserImpl(packet_in buffe
     state start {
         parsed_hdr_2.ethernet.setInvalid();
         parsed_hdr_2.ipv4.setInvalid();
-        user_meta_2 = user_meta;
+        {
+            {
+            }
+        }
         buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
         transition select(parsed_hdr_2.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -51,8 +54,14 @@ parser IngressParserImpl(packet_in buffe
         transition start_0;
     }
     state start_0 {
-        parsed_hdr = parsed_hdr_2;
-        user_meta = user_meta_2;
+        {
+            parsed_hdr.ethernet = parsed_hdr_2.ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
+        }
+        {
+            {
+            }
+        }
         transition accept;
     }
 }
@@ -62,7 +71,10 @@ parser EgressParserImpl(packet_in buffer
     state start {
         parsed_hdr_3.ethernet.setInvalid();
         parsed_hdr_3.ipv4.setInvalid();
-        user_meta_3 = user_meta;
+        {
+            {
+            }
+        }
         buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
         transition select(parsed_hdr_3.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
@@ -74,8 +86,14 @@ parser EgressParserImpl(packet_in buffer
         transition start_1;
     }
     state start_1 {
-        parsed_hdr = parsed_hdr_3;
-        user_meta = user_meta_3;
+        {
+            parsed_hdr.ethernet = parsed_hdr_3.ethernet;
+            parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
+        }
+        {
+            {
+            }
+        }
         transition accept;
     }
 }
@@ -88,20 +106,52 @@ control ingress(inout headers hdr, inout
     @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
         per_prefix_pkt_byte_count.count();
         {
-            meta_0 = ostd;
+            {
+                meta_0.class_of_service = ostd.class_of_service;
+                meta_0.clone = ostd.clone;
+                meta_0.clone_session_id = ostd.clone_session_id;
+                meta_0.drop = ostd.drop;
+                meta_0.resubmit = ostd.resubmit;
+                meta_0.multicast_group = ostd.multicast_group;
+                meta_0.egress_port = ostd.egress_port;
+            }
             egress_port_0 = oport;
             meta_0.drop = false;
             meta_0.multicast_group = 10w0;
             meta_0.egress_port = egress_port_0;
-            ostd = meta_0;
+            {
+                ostd.class_of_service = meta_0.class_of_service;
+                ostd.clone = meta_0.clone;
+                ostd.clone_session_id = meta_0.clone_session_id;
+                ostd.drop = meta_0.drop;
+                ostd.resubmit = meta_0.resubmit;
+                ostd.multicast_group = meta_0.multicast_group;
+                ostd.egress_port = meta_0.egress_port;
+            }
         }
     }
     @name("ingress.default_route_drop") action default_route_drop_0() {
         per_prefix_pkt_byte_count.count();
         {
-            meta_1 = ostd;
+            {
+                meta_1.class_of_service = ostd.class_of_service;
+                meta_1.clone = ostd.clone;
+                meta_1.clone_session_id = ostd.clone_session_id;
+                meta_1.drop = ostd.drop;
+                meta_1.resubmit = ostd.resubmit;
+                meta_1.multicast_group = ostd.multicast_group;
+                meta_1.egress_port = ostd.egress_port;
+            }
             meta_1.drop = true;
-            ostd = meta_1;
+            {
+                ostd.class_of_service = meta_1.class_of_service;
+                ostd.clone = meta_1.clone;
+                ostd.clone_session_id = meta_1.clone_session_id;
+                ostd.drop = meta_1.drop;
+                ostd.resubmit = meta_1.resubmit;
+                ostd.multicast_group = meta_1.multicast_group;
+                ostd.egress_port = meta_1.egress_port;
+            }
         }
     }
     @name("ingress.ipv4_da_lpm") table ipv4_da_lpm {
