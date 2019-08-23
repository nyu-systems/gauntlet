--- before_pass
+++ after_pass
@@ -36,9 +36,6 @@ parser parserImpl(packet_in packet, out
     @name("parserImpl.p1.ipv4_ethertypes") value_set<bit<16>>(8) p1_ipv4_ethertypes;
     @name("parserImpl.p2.ipv4_ethertypes") value_set<bit<16>>(8) p2_ipv4_ethertypes;
     state start {
-        transition subParser_start;
-    }
-    state subParser_start {
         packet.extract<ethernet_t>(hdr.ethernet_1);
         transition select(hdr.ethernet_1.etherType) {
             p1_ipv4_ethertypes: subParser_parse_ipv4;
@@ -50,9 +47,6 @@ parser parserImpl(packet_in packet, out
         transition start_0;
     }
     state start_0 {
-        transition subParser_start_0;
-    }
-    state subParser_start_0 {
         packet.extract<ethernet_t>(hdr.ethernet_2);
         transition select(hdr.ethernet_2.etherType) {
             p2_ipv4_ethertypes: subParser_parse_ipv4_0;
