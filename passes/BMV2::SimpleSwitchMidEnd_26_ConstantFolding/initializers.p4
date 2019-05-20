*** dumps/p4_16_samples/initializers.p4/pruned/initializers-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:32.101353700 +0200
--- dumps/p4_16_samples/initializers.p4/pruned/initializers-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:58:32.103963700 +0200
*************** parser P() {
*** 15,21 ****
  control C() {
      @name("C.fake") Fake() fake_2;
      apply {
!         fake_2.call(32w0 + 32w1);
      }
  }
  parser SimpleParser();
--- 15,21 ----
  control C() {
      @name("C.fake") Fake() fake_2;
      apply {
!         fake_2.call(32w1);
      }
  }
  parser SimpleParser();
