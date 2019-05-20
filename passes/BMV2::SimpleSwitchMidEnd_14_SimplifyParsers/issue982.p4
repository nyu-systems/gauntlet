*** dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:39.599770400 +0200
--- dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 16:59:39.607787800 +0200
*************** parser EgressParserImpl(packet_in buffer
*** 204,212 ****
          parsed_hdr_2.ethernet.setInvalid();
          parsed_hdr_2.ipv4.setInvalid();
          user_meta_3 = user_meta;
-         transition CommonParser_start;
-     }
-     state CommonParser_start {
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
          transition select(parsed_hdr_2.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
--- 204,209 ----
*************** parser EgressParserImpl(packet_in buffer
*** 225,233 ****
      state parse_clone_header {
          istd_1 = istd;
          user_meta_4 = user_meta;
-         transition CloneParser_start;
-     }
-     state CloneParser_start {
          transition select(istd_1.clone_metadata.type) {
              3w0: CloneParser_parse_clone_header;
              3w1: CloneParser_parse_clone_header_0;
--- 222,227 ----
*************** parser IngressParserImpl(packet_in buffe
*** 280,288 ****
          parsed_hdr_3.ethernet.setInvalid();
          parsed_hdr_3.ipv4.setInvalid();
          user_meta_5 = user_meta;
-         transition CommonParser_start_0;
-     }
-     state CommonParser_start_0 {
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
          transition select(parsed_hdr_3.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
--- 274,279 ----
