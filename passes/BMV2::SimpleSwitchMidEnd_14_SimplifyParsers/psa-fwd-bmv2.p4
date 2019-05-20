*** dumps/p4_16_samples/psa-fwd-bmv2.p4/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:00:08.947906500 +0200
--- dumps/p4_16_samples/psa-fwd-bmv2.p4/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:00:08.951056000 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 22,34 ****
      state start {
          parsed_hdr_2.ethernet.setInvalid();
          user_meta_2 = user_meta;
-         transition CommonParser_start;
-     }
-     state CommonParser_start {
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
-         transition start_0;
-     }
-     state start_0 {
          parsed_hdr = parsed_hdr_2;
          user_meta = user_meta_2;
          transition accept;
--- 22,28 ----
*************** parser EgressParserImpl(packet_in buffer
*** 40,52 ****
      state start {
          parsed_hdr_3.ethernet.setInvalid();
          user_meta_3 = user_meta;
-         transition CommonParser_start_0;
-     }
-     state CommonParser_start_0 {
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
-         transition start_1;
-     }
-     state start_1 {
          parsed_hdr = parsed_hdr_3;
          user_meta = user_meta_3;
          transition accept;
--- 34,40 ----
