*** dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:45.358764000 +0200
--- dumps/p4_16_samples/issue1412-bmv2.p4/pruned/issue1412-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:45.361088100 +0200
*************** control IngressImpl(inout headers_t hdr,
*** 20,35 ****
      }
  }
  control EgressImpl(inout headers_t hdr, inout metadata meta, inout standard_metadata_t ostd) {
-     bool cond_0;
-     bool pred;
      @name(".NoAction") action NoAction_0() {
      }
      @name("EgressImpl.set_true") action set_true_0() {
          {
              {
!                 cond_0 = meta.field == 8w0;
!                 pred = cond_0;
!                 meta.cond = (pred ? true : meta.cond);
              }
          }
      }
--- 20,31 ----
      }
  }
  control EgressImpl(inout headers_t hdr, inout metadata meta, inout standard_metadata_t ostd) {
      @name(".NoAction") action NoAction_0() {
      }
      @name("EgressImpl.set_true") action set_true_0() {
          {
              {
!                 meta.cond = (meta.field == 8w0 ? true : meta.cond);
              }
          }
      }
