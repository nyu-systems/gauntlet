*** dumps/p4_16_samples/initializers.p4/pruned/initializers-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:32.099252000 +0200
--- dumps/p4_16_samples/initializers.p4/pruned/initializers-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:32.101353700 +0200
*************** parser P() {
*** 13,25 ****
      }
  }
  control C() {
-     bit<32> x_2;
-     bit<32> y;
      @name("C.fake") Fake() fake_2;
      apply {
!         x_2 = 32w0;
!         y = x_2 + 32w1;
!         fake_2.call(y);
      }
  }
  parser SimpleParser();
--- 13,21 ----
      }
  }
  control C() {
      @name("C.fake") Fake() fake_2;
      apply {
!         fake_2.call(32w0 + 32w1);
      }
  }
  parser SimpleParser();
