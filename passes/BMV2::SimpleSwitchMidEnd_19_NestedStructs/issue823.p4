*** dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:29.156776100 +0200
--- dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:59:29.280928900 +0200
*************** struct headers_t {
*** 9,17 ****
      data_h data;
  }
  parser MyP1(packet_in pkt, out headers_t hdr) {
!     headers_t hdr_1;
      state start {
!         hdr_1.data.setInvalid();
          transition reject;
      }
  }
--- 9,17 ----
      data_h data;
  }
  parser MyP1(packet_in pkt, out headers_t hdr) {
!     data_h hdr_1_data;
      state start {
!         hdr_1_data.setInvalid();
          transition reject;
      }
  }
