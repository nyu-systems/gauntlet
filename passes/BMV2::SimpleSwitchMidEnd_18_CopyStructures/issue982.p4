*** dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:59:39.619487200 +0200
--- dumps/p4_16_samples/issue982.p4/pruned/issue982-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:39.626572600 +0200
*************** parser EgressParserImpl(packet_in buffer
*** 203,209 ****
      state parse_ethernet {
          parsed_hdr_2.ethernet.setInvalid();
          parsed_hdr_2.ipv4.setInvalid();
!         user_meta_3 = user_meta;
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
          transition select(parsed_hdr_2.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
--- 203,216 ----
      state parse_ethernet {
          parsed_hdr_2.ethernet.setInvalid();
          parsed_hdr_2.ipv4.setInvalid();
!         {
!             {
!                 user_meta_3.fwd_metadata.outport = user_meta.fwd_metadata.outport;
!             }
!             user_meta_3.custom_clone_id = user_meta.custom_clone_id;
!             user_meta_3.clone_0 = user_meta.clone_0;
!             user_meta_3.clone_1 = user_meta.clone_1;
!         }
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
          transition select(parsed_hdr_2.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
*************** parser EgressParserImpl(packet_in buffer
*** 215,227 ****
          transition parse_ethernet_0;
      }
      state parse_ethernet_0 {
!         parsed_hdr = parsed_hdr_2;
!         user_meta = user_meta_3;
          transition accept;
      }
      state parse_clone_header {
!         istd_1 = istd;
!         user_meta_4 = user_meta;
          transition select(istd_1.clone_metadata.type) {
              3w0: CloneParser_parse_clone_header;
              3w1: CloneParser_parse_clone_header_0;
--- 222,261 ----
          transition parse_ethernet_0;
      }
      state parse_ethernet_0 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_2.ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
!         }
!         {
!             {
!                 user_meta.fwd_metadata.outport = user_meta_3.fwd_metadata.outport;
!             }
!             user_meta.custom_clone_id = user_meta_3.custom_clone_id;
!             user_meta.clone_0 = user_meta_3.clone_0;
!             user_meta.clone_1 = user_meta_3.clone_1;
!         }
          transition accept;
      }
      state parse_clone_header {
!         {
!             istd_1.egress_port = istd.egress_port;
!             istd_1.instance_type = istd.instance_type;
!             {
!                 istd_1.clone_metadata.type = istd.clone_metadata.type;
!                 {
!                     istd_1.clone_metadata.data.h0 = istd.clone_metadata.data.h0;
!                     istd_1.clone_metadata.data.h1 = istd.clone_metadata.data.h1;
!                 }
!             }
!         }
!         {
!             {
!                 user_meta_4.fwd_metadata.outport = user_meta.fwd_metadata.outport;
!             }
!             user_meta_4.custom_clone_id = user_meta.custom_clone_id;
!             user_meta_4.clone_0 = user_meta.clone_0;
!             user_meta_4.clone_1 = user_meta.clone_1;
!         }
          transition select(istd_1.clone_metadata.type) {
              3w0: CloneParser_parse_clone_header;
              3w1: CloneParser_parse_clone_header_0;
*************** parser EgressParserImpl(packet_in buffer
*** 239,245 ****
          transition parse_clone_header_2;
      }
      state parse_clone_header_2 {
!         user_meta = user_meta_4;
          transition parse_ethernet;
      }
  }
--- 273,286 ----
          transition parse_clone_header_2;
      }
      state parse_clone_header_2 {
!         {
!             {
!                 user_meta.fwd_metadata.outport = user_meta_4.fwd_metadata.outport;
!             }
!             user_meta.custom_clone_id = user_meta_4.custom_clone_id;
!             user_meta.clone_0 = user_meta_4.clone_0;
!             user_meta.clone_1 = user_meta_4.clone_1;
!         }
          transition parse_ethernet;
      }
  }
*************** parser IngressParserImpl(packet_in buffe
*** 273,279 ****
      state start {
          parsed_hdr_3.ethernet.setInvalid();
          parsed_hdr_3.ipv4.setInvalid();
!         user_meta_5 = user_meta;
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
          transition select(parsed_hdr_3.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
--- 314,327 ----
      state start {
          parsed_hdr_3.ethernet.setInvalid();
          parsed_hdr_3.ipv4.setInvalid();
!         {
!             {
!                 user_meta_5.fwd_metadata.outport = user_meta.fwd_metadata.outport;
!             }
!             user_meta_5.custom_clone_id = user_meta.custom_clone_id;
!             user_meta_5.clone_0 = user_meta.clone_0;
!             user_meta_5.clone_1 = user_meta.clone_1;
!         }
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
          transition select(parsed_hdr_3.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
*************** parser IngressParserImpl(packet_in buffe
*** 285,292 ****
          transition start_0;
      }
      state start_0 {
!         parsed_hdr = parsed_hdr_3;
!         user_meta = user_meta_5;
          transition accept;
      }
  }
--- 333,350 ----
          transition start_0;
      }
      state start_0 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_3.ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
!         }
!         {
!             {
!                 user_meta.fwd_metadata.outport = user_meta_5.fwd_metadata.outport;
!             }
!             user_meta.custom_clone_id = user_meta_5.custom_clone_id;
!             user_meta.clone_0 = user_meta_5.clone_0;
!             user_meta.clone_1 = user_meta_5.clone_1;
!         }
          transition accept;
      }
  }
*************** control IngressDeparserImpl(packet_out p
*** 316,325 ****
      clone_metadata_t clone_md;
      apply {
          clone_md.data.h1.setValid();
!         clone_md.data.h1 = { 32w0 };
          clone_md.type = 3w0;
!         if (meta.custom_clone_id == 3w1) 
!             ostd.clone_metadata = clone_md;
          packet.emit<ethernet_t>(hdr.ethernet);
          packet.emit<ipv4_t>(hdr.ipv4);
      }
--- 374,390 ----
      clone_metadata_t clone_md;
      apply {
          clone_md.data.h1.setValid();
!         {
!             clone_md.data.h1.data = 32w0;
!         }
          clone_md.type = 3w0;
!         if (meta.custom_clone_id == 3w1) {
!             ostd.clone_metadata.type = clone_md.type;
!             {
!                 ostd.clone_metadata.data.h0 = clone_md.data.h0;
!                 ostd.clone_metadata.data.h1 = clone_md.data.h1;
!             }
!         }
          packet.emit<ethernet_t>(hdr.ethernet);
          packet.emit<ipv4_t>(hdr.ipv4);
      }
