*** dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:58:45.351663000 +0200
--- dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:58:45.354025500 +0200
*************** control EgressImpl(inout headers_t hdr,
*** 23,30 ****
      @name(".NoAction") action NoAction_0() {
      }
      @name("EgressImpl.set_true") action set_true_0() {
!         if (meta.field == 8w0) 
!             meta.cond = true;
      }
      @name("EgressImpl.change_cond") table change_cond {
          key = {
--- 23,37 ----
      @name(".NoAction") action NoAction_0() {
      }
      @name("EgressImpl.set_true") action set_true_0() {
!         {
!             bool cond_0;
!             {
!                 bool pred;
!                 cond_0 = meta.field == 8w0;
!                 pred = cond_0;
!                 meta.cond = (pred ? true : meta.cond);
!             }
!         }
      }
      @name("EgressImpl.change_cond") table change_cond {
          key = {
