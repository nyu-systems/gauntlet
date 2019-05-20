*** dumps/p4_16_samples/named-arg.p4/pruned/named-arg-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-05-20 16:59:47.812394700 +0200
--- dumps/p4_16_samples/named-arg.p4/pruned/named-arg-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-05-20 16:59:47.815322500 +0200
*************** control c() {
*** 5,11 ****
      apply {
          xv = 16w0;
          b = true;
!         f(y = b, x = xv);
      }
  }
  control empty();
--- 5,11 ----
      apply {
          xv = 16w0;
          b = true;
!         f(x = xv, y = b);
      }
  }
  control empty();
