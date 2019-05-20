*** dumps/p4_16_samples/psa-fwd-bmv2.p4/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:09.033941900 +0200
--- dumps/p4_16_samples/psa-fwd-bmv2.p4/pruned/psa-fwd-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:09.116964100 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 21,38 ****
      fwd_metadata_t user_meta_2_fwd_metadata;
      state start {
          parsed_hdr_2_ethernet.setInvalid();
-         {
-             {
-             }
-         }
          buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
!         {
!             parsed_hdr.ethernet = parsed_hdr_2_ethernet;
!         }
!         {
!             {
!             }
!         }
          transition accept;
      }
  }
--- 21,28 ----
      fwd_metadata_t user_meta_2_fwd_metadata;
      state start {
          parsed_hdr_2_ethernet.setInvalid();
          buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
!         parsed_hdr.ethernet = parsed_hdr_2_ethernet;
          transition accept;
      }
  }
*************** parser EgressParserImpl(packet_in buffer
*** 41,58 ****
      fwd_metadata_t user_meta_3_fwd_metadata;
      state start {
          parsed_hdr_3_ethernet.setInvalid();
-         {
-             {
-             }
-         }
          buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
!         {
!             parsed_hdr.ethernet = parsed_hdr_3_ethernet;
!         }
!         {
!             {
!             }
!         }
          transition accept;
      }
  }
--- 31,38 ----
      fwd_metadata_t user_meta_3_fwd_metadata;
      state start {
          parsed_hdr_3_ethernet.setInvalid();
          buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
!         parsed_hdr.ethernet = parsed_hdr_3_ethernet;
          transition accept;
      }
  }
