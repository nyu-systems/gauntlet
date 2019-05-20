*** dumps/p4_16_samples/def-use.p4/pruned/def-use-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:11.103293800 +0200
--- dumps/p4_16_samples/def-use.p4/pruned/def-use-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:11.132475800 +0200
*************** control IngressI(inout H hdr, inout M me
*** 15,20 ****
--- 15,21 ----
      }
  }
  control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
+     bool hasReturned_0;
      @name("EgressI.a") action a_0() {
      }
      @name("EgressI.t") table t {
*************** control EgressI(inout H hdr, inout M met
*** 26,32 ****
          default_action = a_0();
      }
      apply {
!         bool hasReturned_0 = false;
          switch (t.apply().action_run) {
              a_0: {
                  hasReturned_0 = true;
--- 27,33 ----
          default_action = a_0();
      }
      apply {
!         hasReturned_0 = false;
          switch (t.apply().action_run) {
              a_0: {
                  hasReturned_0 = true;
