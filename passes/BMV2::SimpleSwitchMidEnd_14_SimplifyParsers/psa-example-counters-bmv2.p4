--- dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:31:43.395059900 +0200
+++ dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:31:43.398593800 +0200
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
