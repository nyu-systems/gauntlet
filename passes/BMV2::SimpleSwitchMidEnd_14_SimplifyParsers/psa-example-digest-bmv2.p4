--- dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:31:44.865594500 +0200
+++ dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:31:44.869194100 +0200
@@ -42,9 +42,6 @@ parser IngressParserImpl(packet_in buffe
         parsed_hdr_2.ethernet.setInvalid();
         parsed_hdr_2.ipv4.setInvalid();
         meta_0 = meta;
-        transition CommonParser_start;
-    }
-    state CommonParser_start {
         buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
         transition select(parsed_hdr_2.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -68,9 +65,6 @@ parser EgressParserImpl(packet_in buffer
         parsed_hdr_3.ethernet.setInvalid();
         parsed_hdr_3.ipv4.setInvalid();
         meta_5 = meta;
-        transition CommonParser_start_0;
-    }
-    state CommonParser_start_0 {
         buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
         transition select(parsed_hdr_3.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
