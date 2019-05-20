*** dumps/p4_16_samples/psa-fwd-bmv2.p4/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:08.968352700 +0200
--- dumps/p4_16_samples/psa-fwd-bmv2.p4/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:08.974516700 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 21,30 ****
      metadata user_meta_2;
      state start {
          parsed_hdr_2.ethernet.setInvalid();
!         user_meta_2 = user_meta;
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
!         parsed_hdr = parsed_hdr_2;
!         user_meta = user_meta_2;
          transition accept;
      }
  }
--- 21,38 ----
      metadata user_meta_2;
      state start {
          parsed_hdr_2.ethernet.setInvalid();
!         {
!             {
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
!         {
!             parsed_hdr.ethernet = parsed_hdr_2.ethernet;
!         }
!         {
!             {
!             }
!         }
          transition accept;
      }
  }
*************** parser EgressParserImpl(packet_in buffer
*** 33,42 ****
      metadata user_meta_3;
      state start {
          parsed_hdr_3.ethernet.setInvalid();
!         user_meta_3 = user_meta;
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
!         parsed_hdr = parsed_hdr_3;
!         user_meta = user_meta_3;
          transition accept;
      }
  }
--- 41,58 ----
      metadata user_meta_3;
      state start {
          parsed_hdr_3.ethernet.setInvalid();
!         {
!             {
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
!         {
!             parsed_hdr.ethernet = parsed_hdr_3.ethernet;
!         }
!         {
!             {
!             }
!         }
          transition accept;
      }
  }
