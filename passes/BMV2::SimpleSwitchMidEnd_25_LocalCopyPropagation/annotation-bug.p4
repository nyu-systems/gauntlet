*** dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:48.204830600 +0200
--- dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:48.208060100 +0200
*************** struct tuple_0 {
*** 15,26 ****
  extern bit<16> get<T>(in T data);
  control cc() {
      ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
-     ipv4_option_timestamp_t tmp_0_ipv4_option_timestamp;
      apply {
          {
-             tmp_0_ipv4_option_timestamp = hdr_1_ipv4_option_timestamp;
          }
!         get<headers>({ tmp_0_ipv4_option_timestamp });
      }
  }
  control C();
--- 15,24 ----
  extern bit<16> get<T>(in T data);
  control cc() {
      ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
      apply {
          {
          }
!         get<headers>({ hdr_1_ipv4_option_timestamp });
      }
  }
  control C();
