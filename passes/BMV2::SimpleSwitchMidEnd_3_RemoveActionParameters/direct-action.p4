*** dumps/p4_16_samples/direct-action.p4/pruned/direct-action-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:12.652180700 +0200
--- dumps/p4_16_samples/direct-action.p4/pruned/direct-action-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:12.674731200 +0200
***************
*** 1,11 ****
  control c(inout bit<16> y) {
      bit<32> x;
!     @name("c.a") action a_0(in bit<32> arg) {
          y = (bit<16>)arg;
      }
      apply {
          x = 32w2;
!         a_0(x);
      }
  }
  control proto(inout bit<16> y);
--- 1,13 ----
  control c(inout bit<16> y) {
      bit<32> x;
!     bit<32> arg;
!     @name("c.a") action a_0() {
!         arg = x;
          y = (bit<16>)arg;
      }
      apply {
          x = 32w2;
!         a_0();
      }
  }
  control proto(inout bit<16> y);
