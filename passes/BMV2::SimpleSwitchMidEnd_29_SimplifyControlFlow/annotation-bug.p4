*** dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:57:48.220008200 +0200
--- dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:57:48.284000900 +0200
*************** extern bit<16> get<T>(in T data);
*** 16,23 ****
  control cc() {
      ipv4_option_timestamp_t hdr_1_ipv4_option_timestamp;
      apply {
-         {
-         }
          get<headers>({ hdr_1_ipv4_option_timestamp });
      }
  }
--- 16,21 ----
