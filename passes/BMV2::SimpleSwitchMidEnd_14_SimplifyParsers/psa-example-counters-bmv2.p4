--- dumps/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:33:16.552413700 +0200
+++ dumps/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:33:16.556296700 +0200
@@ -40,9 +40,6 @@ parser IngressParserImpl(packet_in buffe
         parsed_hdr_2.ethernet.setInvalid();
         parsed_hdr_2.ipv4.setInvalid();
         user_meta_2 = user_meta;
-        transition CommonParser_start;
-    }
-    state CommonParser_start {
         buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
         transition select(parsed_hdr_2.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -66,9 +63,6 @@ parser EgressParserImpl(packet_in buffer
         parsed_hdr_3.ethernet.setInvalid();
         parsed_hdr_3.ipv4.setInvalid();
         user_meta_3 = user_meta;
-        transition CommonParser_start_0;
-    }
-    state CommonParser_start_0 {
         buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
         transition select(parsed_hdr_3.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
