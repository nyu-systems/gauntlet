*** dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:49.242829800 +0200
--- dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:49.246680700 +0200
*************** control c(inout bit<1> r) {
*** 15,22 ****
      T s_0_f1_field;
      T s_0_f1_field_0;
      T s_0_f2;
-     bit<1> s_0_z;
-     bit<1> tmp;
      apply {
          {
              {
--- 15,20 ----
*************** control c(inout bit<1> r) {
*** 30,40 ****
              {
                  s_0_f2.f = 1w0;
              }
-             s_0_z = 1w1;
          }
          f<tuple_0>({ s_0_f1_field, s_0_f1_field_0 });
!         tmp = s_0_f2.f & s_0_z;
!         r = tmp;
      }
  }
  control simple(inout bit<1> r);
--- 28,36 ----
              {
                  s_0_f2.f = 1w0;
              }
          }
          f<tuple_0>({ s_0_f1_field, s_0_f1_field_0 });
!         r = s_0_f2.f & 1w1;
      }
  }
  control simple(inout bit<1> r);
