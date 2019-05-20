*** dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:57:47.055322100 +0200
--- dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:57:47.080474900 +0200
***************
*** 1,9 ****
  control c(inout bit<32> x) {
!     @name("c.a") action a_0(in bit<32> arg_1) {
          x = arg_1;
      }
      apply {
!         a_0(32w15);
      }
  }
  control proto(inout bit<32> arg);
--- 1,11 ----
  control c(inout bit<32> x) {
!     bit<32> arg_1;
!     @name("c.a") action a_0() {
!         arg_1 = 32w15;
          x = arg_1;
      }
      apply {
!         a_0();
      }
  }
  control proto(inout bit<32> arg);
