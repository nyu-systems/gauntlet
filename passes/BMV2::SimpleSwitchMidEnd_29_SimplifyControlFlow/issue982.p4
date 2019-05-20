*** dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:39.670392200 +0200
--- dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:39.742779200 +0200
*************** parser EgressParserImpl(packet_in buffer
*** 213,226 ****
      state parse_ethernet {
          parsed_hdr_2_ethernet.setInvalid();
          parsed_hdr_2_ipv4.setInvalid();
!         {
!             {
!                 user_meta_3_fwd_metadata.outport = user_meta.fwd_metadata.outport;
!             }
!             user_meta_3_custom_clone_id = user_meta.custom_clone_id;
!             user_meta_3_clone = user_meta.clone_0;
!             user_meta_3_clone_0 = user_meta.clone_1;
!         }
          buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
          transition select(parsed_hdr_2_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
--- 213,222 ----
      state parse_ethernet {
          parsed_hdr_2_ethernet.setInvalid();
          parsed_hdr_2_ipv4.setInvalid();
!         user_meta_3_fwd_metadata.outport = user_meta.fwd_metadata.outport;
!         user_meta_3_custom_clone_id = user_meta.custom_clone_id;
!         user_meta_3_clone = user_meta.clone_0;
!         user_meta_3_clone_0 = user_meta.clone_1;
          buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
          transition select(parsed_hdr_2_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
*************** parser EgressParserImpl(packet_in buffer
*** 232,271 ****
          transition parse_ethernet_0;
      }
      state parse_ethernet_0 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_2_ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
!         }
!         {
!             {
!                 user_meta.fwd_metadata.outport = user_meta_3_fwd_metadata.outport;
!             }
!             user_meta.custom_clone_id = user_meta_3_custom_clone_id;
!             user_meta.clone_0 = user_meta_3_clone;
!             user_meta.clone_1 = user_meta_3_clone_0;
!         }
          transition accept;
      }
      state parse_clone_header {
!         {
!             istd_1_egress_port = istd.egress_port;
!             istd_1_instance_type = istd.instance_type;
!             {
!                 istd_1_clone_metadata_type = istd.clone_metadata.type;
!                 {
!                     istd_1_clone_metadata_data.h0 = istd.clone_metadata.data.h0;
!                     istd_1_clone_metadata_data.h1 = istd.clone_metadata.data.h1;
!                 }
!             }
!         }
!         {
!             {
!                 user_meta_4_fwd_metadata.outport = user_meta.fwd_metadata.outport;
!             }
!             user_meta_4_custom_clone_id = user_meta.custom_clone_id;
!             user_meta_4_clone = user_meta.clone_0;
!             user_meta_4_clone_0 = user_meta.clone_1;
!         }
          transition select(istd_1_clone_metadata_type) {
              3w0: CloneParser_parse_clone_header;
              3w1: CloneParser_parse_clone_header_0;
--- 228,251 ----
          transition parse_ethernet_0;
      }
      state parse_ethernet_0 {
!         parsed_hdr.ethernet = parsed_hdr_2_ethernet;
!         parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
!         user_meta.fwd_metadata.outport = user_meta_3_fwd_metadata.outport;
!         user_meta.custom_clone_id = user_meta_3_custom_clone_id;
!         user_meta.clone_0 = user_meta_3_clone;
!         user_meta.clone_1 = user_meta_3_clone_0;
          transition accept;
      }
      state parse_clone_header {
!         istd_1_egress_port = istd.egress_port;
!         istd_1_instance_type = istd.instance_type;
!         istd_1_clone_metadata_type = istd.clone_metadata.type;
!         istd_1_clone_metadata_data.h0 = istd.clone_metadata.data.h0;
!         istd_1_clone_metadata_data.h1 = istd.clone_metadata.data.h1;
!         user_meta_4_fwd_metadata.outport = user_meta.fwd_metadata.outport;
!         user_meta_4_custom_clone_id = user_meta.custom_clone_id;
!         user_meta_4_clone = user_meta.clone_0;
!         user_meta_4_clone_0 = user_meta.clone_1;
          transition select(istd_1_clone_metadata_type) {
              3w0: CloneParser_parse_clone_header;
              3w1: CloneParser_parse_clone_header_0;
*************** parser EgressParserImpl(packet_in buffer
*** 283,296 ****
          transition parse_clone_header_2;
      }
      state parse_clone_header_2 {
!         {
!             {
!                 user_meta.fwd_metadata.outport = user_meta_4_fwd_metadata.outport;
!             }
!             user_meta.custom_clone_id = user_meta_4_custom_clone_id;
!             user_meta.clone_0 = user_meta_4_clone;
!             user_meta.clone_1 = user_meta_4_clone_0;
!         }
          transition parse_ethernet;
      }
  }
--- 263,272 ----
          transition parse_clone_header_2;
      }
      state parse_clone_header_2 {
!         user_meta.fwd_metadata.outport = user_meta_4_fwd_metadata.outport;
!         user_meta.custom_clone_id = user_meta_4_custom_clone_id;
!         user_meta.clone_0 = user_meta_4_clone;
!         user_meta.clone_1 = user_meta_4_clone_0;
          transition parse_ethernet;
      }
  }
*************** parser IngressParserImpl(packet_in buffe
*** 328,341 ****
      state start {
          parsed_hdr_3_ethernet.setInvalid();
          parsed_hdr_3_ipv4.setInvalid();
!         {
!             {
!                 user_meta_5_fwd_metadata.outport = user_meta.fwd_metadata.outport;
!             }
!             user_meta_5_custom_clone_id = user_meta.custom_clone_id;
!             user_meta_5_clone = user_meta.clone_0;
!             user_meta_5_clone_0 = user_meta.clone_1;
!         }
          buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
          transition select(parsed_hdr_3_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
--- 304,313 ----
      state start {
          parsed_hdr_3_ethernet.setInvalid();
          parsed_hdr_3_ipv4.setInvalid();
!         user_meta_5_fwd_metadata.outport = user_meta.fwd_metadata.outport;
!         user_meta_5_custom_clone_id = user_meta.custom_clone_id;
!         user_meta_5_clone = user_meta.clone_0;
!         user_meta_5_clone_0 = user_meta.clone_1;
          buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
          transition select(parsed_hdr_3_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
*************** parser IngressParserImpl(packet_in buffe
*** 347,364 ****
          transition start_0;
      }
      state start_0 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_3_ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
!         }
!         {
!             {
!                 user_meta.fwd_metadata.outport = user_meta_5_fwd_metadata.outport;
!             }
!             user_meta.custom_clone_id = user_meta_5_custom_clone_id;
!             user_meta.clone_0 = user_meta_5_clone;
!             user_meta.clone_1 = user_meta_5_clone_0;
!         }
          transition accept;
      }
  }
--- 319,330 ----
          transition start_0;
      }
      state start_0 {
!         parsed_hdr.ethernet = parsed_hdr_3_ethernet;
!         parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
!         user_meta.fwd_metadata.outport = user_meta_5_fwd_metadata.outport;
!         user_meta.custom_clone_id = user_meta_5_custom_clone_id;
!         user_meta.clone_0 = user_meta_5_clone;
!         user_meta.clone_1 = user_meta_5_clone_0;
          transition accept;
      }
  }
*************** control IngressDeparserImpl(packet_out p
*** 388,402 ****
      clone_union_t clone_md_data;
      apply {
          clone_md_data.h1.setValid();
!         {
!             clone_md_data.h1.data = 32w0;
!         }
          if (meta.custom_clone_id == 3w1) {
              ostd.clone_metadata.type = 3w0;
!             {
!                 ostd.clone_metadata.data.h0 = clone_md_data.h0;
!                 ostd.clone_metadata.data.h1 = clone_md_data.h1;
!             }
          }
          packet.emit<ethernet_t>(hdr.ethernet);
          packet.emit<ipv4_t>(hdr.ipv4);
--- 354,364 ----
      clone_union_t clone_md_data;
      apply {
          clone_md_data.h1.setValid();
!         clone_md_data.h1.data = 32w0;
          if (meta.custom_clone_id == 3w1) {
              ostd.clone_metadata.type = 3w0;
!             ostd.clone_metadata.data.h0 = clone_md_data.h0;
!             ostd.clone_metadata.data.h1 = clone_md_data.h1;
          }
          packet.emit<ethernet_t>(hdr.ethernet);
          packet.emit<ipv4_t>(hdr.ipv4);
