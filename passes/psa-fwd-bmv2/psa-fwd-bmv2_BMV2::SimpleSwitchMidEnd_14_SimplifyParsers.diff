--- before_pass
+++ after_pass
@@ -19,26 +19,14 @@ struct headers {
 parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, in empty_t resubmit_meta, in empty_t recirculate_meta) {
     state start {
         parsed_hdr.ethernet.setInvalid();
-        transition CommonParser_start;
-    }
-    state CommonParser_start {
         buffer.extract<ethernet_t>(parsed_hdr.ethernet);
-        transition start_0;
-    }
-    state start_0 {
         transition accept;
     }
 }
 parser EgressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_egress_parser_input_metadata_t istd, in empty_t normal_meta, in empty_t clone_i2e_meta, in empty_t clone_e2e_meta) {
     state start {
         parsed_hdr.ethernet.setInvalid();
-        transition CommonParser_start_0;
-    }
-    state CommonParser_start_0 {
         buffer.extract<ethernet_t>(parsed_hdr.ethernet);
-        transition start_1;
-    }
-    state start_1 {
         transition accept;
     }
 }
