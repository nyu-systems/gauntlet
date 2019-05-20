*** dumps/p4_16_samples/issue561.p4/pruned/issue561-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:21.304534800 +0200
--- dumps/p4_16_samples/issue561.p4/pruned/issue561-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:21.306984800 +0200
*************** package top(ct _ct);
*** 13,31 ****
  control c(out bit<32> x) {
      U u;
      U[2] u2;
-     bool b_1;
      apply {
!         b_1 = u.isValid();
          u.h1.isValid();
          x = u.h1.f + u.h2.g;
          u.h1.setValid();
          u.h1.f = 32w0;
!         x = x + u.h1.f;
          u.h2.g = 32w0;
!         x = x + u.h2.g;
          u2[0].h1.setValid();
          u2[0].h1.f = 32w2;
!         x = x + u2[1].h2.g + u2[0].h1.f;
      }
  }
  top(c()) main;
--- 13,30 ----
  control c(out bit<32> x) {
      U u;
      U[2] u2;
      apply {
!         u.isValid();
          u.h1.isValid();
          x = u.h1.f + u.h2.g;
          u.h1.setValid();
          u.h1.f = 32w0;
!         x = x + 32w0;
          u.h2.g = 32w0;
!         x = x + 32w0;
          u2[0].h1.setValid();
          u2[0].h1.f = 32w2;
!         x = x + u2[1].h2.g + 32w2;
      }
  }
  top(c()) main;
