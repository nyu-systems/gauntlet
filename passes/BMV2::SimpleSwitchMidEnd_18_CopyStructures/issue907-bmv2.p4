*** dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:59:36.136692000 +0200
--- dumps/p4_16_samples/issue907-bmv2.p4/pruned/issue907-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:36.142592600 +0200
*************** control Ing(inout Headers headers, inout
*** 16,22 ****
      S s;
      @name("Ing.r") register<S>(32w100) r;
      apply {
!         s = { 32w0 };
          r.write(32w0, s);
      }
  }
--- 16,24 ----
      S s;
      @name("Ing.r") register<S>(32w100) r;
      apply {
!         {
!             s.f = 32w0;
!         }
          r.write(32w0, s);
      }
  }
