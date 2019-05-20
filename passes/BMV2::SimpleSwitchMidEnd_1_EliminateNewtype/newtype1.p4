*** dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_0_CheckTableSize.p4	2019-05-20 16:59:50.083539400 +0200
--- dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-05-20 16:59:50.124436400 +0200
***************
*** 1,14 ****
  typedef bit<9> Narrow_t;
! type Narrow_t Narrow;
  typedef bit<32> Wide_t;
! type Wide_t Wide;
  control c(out bool b) {
      Wide x;
      Narrow y;
      apply {
!         x = (Wide)32w3;
!         y = (Narrow)(Narrow_t)(Wide_t)x;
!         b = y == (Narrow)9w10;
      }
  }
  control ctrl(out bool b);
--- 1,14 ----
  typedef bit<9> Narrow_t;
! typedef Narrow_t Narrow;
  typedef bit<32> Wide_t;
! typedef Wide_t Wide;
  control c(out bool b) {
      Wide x;
      Narrow y;
      apply {
!         x = 32w3;
!         y = (Narrow_t)(Wide_t)x;
!         b = y == 9w10;
      }
  }
  control ctrl(out bool b);
