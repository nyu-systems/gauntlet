*** dumps/p4_16_samples/issue1334.p4/pruned/issue1334-BMV2::SimpleSwitchMidEnd_5_VisitFunctor.p4	2019-05-20 16:58:42.903043400 +0200
--- dumps/p4_16_samples/issue1334.p4/pruned/issue1334-BMV2::SimpleSwitchMidEnd_6_OrderArguments.p4	2019-05-20 16:58:42.905780900 +0200
*************** control c() {
*** 17,28 ****
          f(a = 32w2);
          f(b = 16w1);
          f(a = 32w1, b = 16w2);
!         f(b = 16w2, a = 32w1);
          o.f();
          o.f(a = 32w2);
          o.f(b = 16w1);
          o.f(a = 32w1, b = 16w2);
!         o.f(b = 16w2, a = 32w1);
          z = 32w4294967294;
      }
  }
--- 17,28 ----
          f(a = 32w2);
          f(b = 16w1);
          f(a = 32w1, b = 16w2);
!         f(a = 32w1, b = 16w2);
          o.f();
          o.f(a = 32w2);
          o.f(b = 16w1);
          o.f(a = 32w1, b = 16w2);
!         o.f(a = 32w1, b = 16w2);
          z = 32w4294967294;
      }
  }
