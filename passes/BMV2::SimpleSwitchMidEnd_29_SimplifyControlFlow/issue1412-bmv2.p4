*** dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:45.373116300 +0200
--- dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:45.429863900 +0200
*************** control EgressImpl(inout headers_t hdr,
*** 23,33 ****
      @name(".NoAction") action NoAction_0() {
      }
      @name("EgressImpl.set_true") action set_true_0() {
!         {
!             {
!                 meta.cond = (meta.field == 8w0 ? true : meta.cond);
!             }
!         }
      }
      @name("EgressImpl.change_cond") table change_cond {
          key = {
--- 23,29 ----
      @name(".NoAction") action NoAction_0() {
      }
      @name("EgressImpl.set_true") action set_true_0() {
!         meta.cond = (meta.field == 8w0 ? true : meta.cond);
      }
      @name("EgressImpl.change_cond") table change_cond {
          key = {
