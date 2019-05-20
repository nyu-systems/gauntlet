*** dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:57.811562700 +0200
--- dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:57.814516500 +0200
*************** parser prs(packet_in p, out Headers h) {
*** 14,27 ****
      }
  }
  control c(inout Headers h, inout standard_metadata_t sm) {
-     bit<10> key_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("c.do_act") action do_act_0() {
      }
      @name("c.tns") table tns {
          key = {
!             key_0: exact @name("h.eth.tst[13:4]") ;
          }
          actions = {
              do_act_0();
--- 14,26 ----
      }
  }
  control c(inout Headers h, inout standard_metadata_t sm) {
      @name(".NoAction") action NoAction_0() {
      }
      @name("c.do_act") action do_act_0() {
      }
      @name("c.tns") table tns {
          key = {
!             h.eth.tst[13:4]: exact @name("h.eth.tst[13:4]") ;
          }
          actions = {
              do_act_0();
*************** control c(inout Headers h, inout standar
*** 31,37 ****
      }
      apply {
          {
-             key_0 = h.eth.tst[13:4];
              tns.apply();
          }
      }
--- 30,35 ----
