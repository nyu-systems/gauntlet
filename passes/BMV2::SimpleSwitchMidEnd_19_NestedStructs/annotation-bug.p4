*** dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:57:48.185870500 +0200
--- dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:57:48.188320000 +0200
*************** struct tuple_0 {
*** 14,26 ****
  }
  extern bit<16> get<T>(in T data);
  control cc() {
!     headers hdr_1;
!     headers tmp_0;
      apply {
          {
!             tmp_0.ipv4_option_timestamp = hdr_1.ipv4_option_timestamp;
          }
!         get<headers>(tmp_0);
      }
  }
  control C();
--- 14,26 ----
  }
  extern bit<16> get<T>(in T data);
  control cc() {
!     ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
!     ipv4_option_timestamp_t tmp_0_ipv4_option_timestamp;
      apply {
          {
!             tmp_0_ipv4_option_timestamp = hdr_1_ipv4_option_timestamp;
          }
!         get<headers>({ tmp_0_ipv4_option_timestamp });
      }
  }
  control C();
