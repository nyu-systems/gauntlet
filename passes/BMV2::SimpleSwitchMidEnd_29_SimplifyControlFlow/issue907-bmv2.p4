*** dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:36.176348200 +0200
--- dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:36.231267600 +0200
*************** control Ing(inout Headers headers, inout
*** 16,24 ****
      S s;
      @name("Ing.r") register<S>(32w100) r;
      apply {
!         {
!             s.f = 32w0;
!         }
          r.write(32w0, s);
      }
  }
--- 16,22 ----
      S s;
      @name("Ing.r") register<S>(32w100) r;
      apply {
!         s.f = 32w0;
          r.write(32w0, s);
      }
  }
