--- dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:43.525983900 +0200
+++ dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:43.528732300 +0200
@@ -40,10 +40,6 @@ parser IngressParserImpl(packet_in buffe
     state start {
         parsed_hdr_2_ethernet.setInvalid();
         parsed_hdr_2_ipv4.setInvalid();
-        {
-            {
-            }
-        }
         buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
         transition select(parsed_hdr_2_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -55,14 +51,8 @@ parser IngressParserImpl(packet_in buffe
         transition start_0;
     }
     state start_0 {
-        {
-            parsed_hdr.ethernet = parsed_hdr_2_ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
-        }
-        {
-            {
-            }
-        }
+        parsed_hdr.ethernet = parsed_hdr_2_ethernet;
+        parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
         transition accept;
     }
 }
@@ -73,10 +63,6 @@ parser EgressParserImpl(packet_in buffer
     state start {
         parsed_hdr_3_ethernet.setInvalid();
         parsed_hdr_3_ipv4.setInvalid();
-        {
-            {
-            }
-        }
         buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
         transition select(parsed_hdr_3_ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
@@ -88,14 +74,8 @@ parser EgressParserImpl(packet_in buffer
         transition start_1;
     }
     state start_1 {
-        {
-            parsed_hdr.ethernet = parsed_hdr_3_ethernet;
-            parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
-        }
-        {
-            {
-            }
-        }
+        parsed_hdr.ethernet = parsed_hdr_3_ethernet;
+        parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
         transition accept;
     }
 }
@@ -104,25 +84,13 @@ control ingress(inout headers hdr, inout
     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(32w2) per_prefix_pkt_byte_count;
     @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
         per_prefix_pkt_byte_count.count();
-        {
-            {
-            }
-            {
-                ostd.drop = false;
-                ostd.multicast_group = 10w0;
-                ostd.egress_port = oport;
-            }
-        }
+        ostd.drop = false;
+        ostd.multicast_group = 10w0;
+        ostd.egress_port = oport;
     }
     @name("ingress.default_route_drop") action default_route_drop_0() {
         per_prefix_pkt_byte_count.count();
-        {
-            {
-            }
-            {
-                ostd.drop = true;
-            }
-        }
+        ostd.drop = true;
     }
     @name("ingress.ipv4_da_lpm") table ipv4_da_lpm {
         key = {
