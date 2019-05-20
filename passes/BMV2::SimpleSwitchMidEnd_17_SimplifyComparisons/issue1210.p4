*** dumps/p4_16_samples/issue1210.p4/pruned/issue1210-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:58:41.449891900 +0200
--- dumps/p4_16_samples/issue1210.p4/pruned/issue1210-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:41.452687300 +0200
*************** parser ParserImpl(packet_in packet, out
*** 16,24 ****
  }
  control IngressImpl(inout parsed_headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
      apply {
!         if (meta.foo == meta.bar) 
              meta.foo._v = meta.foo._v + 9w1;
!         if (meta.foo == { 9w192 }) 
              meta.foo._v = meta.foo._v + 9w1;
      }
  }
--- 16,24 ----
  }
  control IngressImpl(inout parsed_headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
      apply {
!         if (true && meta.foo._v == meta.bar._v) 
              meta.foo._v = meta.foo._v + 9w1;
!         if (true && meta.foo._v == 9w192) 
              meta.foo._v = meta.foo._v + 9w1;
      }
  }
