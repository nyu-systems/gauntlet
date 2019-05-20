*** dumps/p4_16_samples/issue1478-bmv2.p4/pruned/issue1478-bmv2-FrontEnd_49_FrontEndLast.p4	2019-05-20 16:58:47.162078500 +0200
--- dumps/p4_16_samples/issue1478-bmv2.p4/pruned/issue1478-bmv2-BMV2::SimpleSwitchMidEnd_0_CheckTableSize.p4	2019-05-20 16:58:47.055494300 +0200
*************** control ingress(inout Headers h, inout M
*** 33,39 ****
      @name(".NoAction") action NoAction_3() {
      }
      @name("ingress.t1") table t1 {
-         size = 3;
          actions = {
              NoAction_0();
          }
--- 33,38 ----
*************** control ingress(inout Headers h, inout M
*** 49,55 ****
          const entries = {
                          9w0 : NoAction_3();
          }
-         size = 10;
          default_action = NoAction_3();
      }
      apply {
--- 48,53 ----
