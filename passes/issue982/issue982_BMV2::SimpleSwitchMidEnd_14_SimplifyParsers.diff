--- before_pass
+++ after_pass
@@ -228,9 +228,6 @@ parser EgressParserImpl(packet_in buffer
     state parse_ethernet {
         parsed_hdr.ethernet.setInvalid();
         parsed_hdr.ipv4.setInvalid();
-        transition CommonParser_start;
-    }
-    state CommonParser_start {
         buffer.extract<ethernet_t>(parsed_hdr.ethernet);
         transition select(parsed_hdr.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4;
@@ -245,9 +242,6 @@ parser EgressParserImpl(packet_in buffer
         transition accept;
     }
     state parse_clone_header {
-        transition CloneParser_start;
-    }
-    state CloneParser_start {
         transition select(istd.clone_metadata.type) {
             3w0: CloneParser_parse_clone_header;
             3w1: CloneParser_parse_clone_header_0;
@@ -296,9 +290,6 @@ parser IngressParserImpl(packet_in buffe
     state start {
         parsed_hdr.ethernet.setInvalid();
         parsed_hdr.ipv4.setInvalid();
-        transition CommonParser_start_0;
-    }
-    state CommonParser_start_0 {
         buffer.extract<ethernet_t>(parsed_hdr.ethernet);
         transition select(parsed_hdr.ethernet.etherType) {
             16w0x800: CommonParser_parse_ipv4_0;
