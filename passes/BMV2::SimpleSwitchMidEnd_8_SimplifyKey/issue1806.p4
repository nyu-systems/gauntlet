*** dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 16:58:57.870494700 +0200
--- dumps/p4_16_samples/issue1806.p4/pruned/issue1806-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 16:58:57.873839200 +0200
*************** control c(inout Headers h, inout standar
*** 18,26 ****
      }
      @name("c.do_act") action do_act_0() {
      }
      @name("c.tns") table tns {
          key = {
!             h.eth.tst[13:4]: exact @name("h.eth.tst[13:4]") ;
          }
          actions = {
              do_act_0();
--- 18,27 ----
      }
      @name("c.do_act") action do_act_0() {
      }
+     bit<10> key_0;
      @name("c.tns") table tns {
          key = {
!             key_0: exact @name("h.eth.tst[13:4]") ;
          }
          actions = {
              do_act_0();
*************** control c(inout Headers h, inout standar
*** 29,35 ****
          default_action = NoAction_0();
      }
      apply {
!         tns.apply();
      }
  }
  parser p<H>(packet_in _p, out H h);
--- 30,39 ----
          default_action = NoAction_0();
      }
      apply {
!         {
!             key_0 = h.eth.tst[13:4];
!             tns.apply();
!         }
      }
  }
  parser p<H>(packet_in _p, out H h);
