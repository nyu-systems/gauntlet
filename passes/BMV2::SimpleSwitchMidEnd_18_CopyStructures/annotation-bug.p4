*** dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:57:48.183369800 +0200
--- dumps/p4_16_samples/annotation-bug.p4/pruned/annotation-bug-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:57:48.185870500 +0200
*************** control cc() {
*** 17,23 ****
      headers hdr_1;
      headers tmp_0;
      apply {
!         tmp_0 = { hdr_1.ipv4_option_timestamp };
          get<headers>(tmp_0);
      }
  }
--- 17,25 ----
      headers hdr_1;
      headers tmp_0;
      apply {
!         {
!             tmp_0.ipv4_option_timestamp = hdr_1.ipv4_option_timestamp;
!         }
          get<headers>(tmp_0);
      }
  }
