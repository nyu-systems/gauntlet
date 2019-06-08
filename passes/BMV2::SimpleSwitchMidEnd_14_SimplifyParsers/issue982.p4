--- dumps/pruned/issue982-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:50.548110900 +0200
+++ dumps/pruned/issue982-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:32:50.549968400 +0200
@@ -204,9 +204,6 @@ parser EgressParserImpl(packet_in buffer
         parsed_hdr_2.ethernet.setInvalid();
         parsed_hdr_2.ipv4.setInvalid();
         user_meta_3 = user_meta;
-        transition CommonParser_start;
-    }
-    state CommonParser_start {
         buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
         transition select(parsed_hdr_2.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -225,9 +222,6 @@ parser EgressParserImpl(packet_in buffer
     state parse_clone_header {
         istd_1 = istd;
         user_meta_4 = user_meta;
-        transition CloneParser_start;
-    }
-    state CloneParser_start {
         transition select(istd_1.clone_metadata.type) {
             3w0: CloneParser_parse_clone_header;
             3w1: CloneParser_parse_clone_header_0;
@@ -280,9 +274,6 @@ parser IngressParserImpl(packet_in buffe
         parsed_hdr_3.ethernet.setInvalid();
         parsed_hdr_3.ipv4.setInvalid();
         user_meta_5 = user_meta;
-        transition CommonParser_start_0;
-    }
-    state CommonParser_start_0 {
         buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
         transition select(parsed_hdr_3.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
