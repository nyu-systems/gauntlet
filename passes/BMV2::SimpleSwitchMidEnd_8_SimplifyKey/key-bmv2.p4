*** dumps/p4_16_samples/key-bmv2.p4/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 16:59:42.917057900 +0200
--- dumps/p4_16_samples/key-bmv2.p4/pruned/key-bmv2-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 16:59:42.919609900 +0200
*************** control ingress(inout Headers h, inout M
*** 38,46 ****
      @name("ingress.c.a") action c_a() {
          h.h.b = h.h.a;
      }
      @name("ingress.c.t") table c_t_0 {
          key = {
!             h.h.a + h.h.a: exact @name("e") ;
          }
          actions = {
              c_a();
--- 38,47 ----
      @name("ingress.c.a") action c_a() {
          h.h.b = h.h.a;
      }
+     bit<32> key_0;
      @name("ingress.c.t") table c_t_0 {
          key = {
!             key_0: exact @name("e") ;
          }
          actions = {
              c_a();
*************** control ingress(inout Headers h, inout M
*** 49,55 ****
          default_action = NoAction_0();
      }
      apply {
!         c_t_0.apply();
          sm.egress_spec = 9w0;
      }
  }
--- 50,59 ----
          default_action = NoAction_0();
      }
      apply {
!         {
!             key_0 = h.h.a + h.h.a;
!             c_t_0.apply();
!         }
          sm.egress_spec = 9w0;
      }
  }
