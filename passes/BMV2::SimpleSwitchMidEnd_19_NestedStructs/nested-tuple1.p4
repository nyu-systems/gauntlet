*** dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:49.221755400 +0200
--- dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:59:49.228520500 +0200
*************** struct S {
*** 12,36 ****
  }
  extern void f<D>(in D data);
  control c(inout bit<1> r) {
!     S s_0;
      bit<1> tmp;
      apply {
          {
              {
                  {
!                     s_0.f1.field.f = 1w0;
                  }
                  {
!                     s_0.f1.field_0.f = 1w1;
                  }
              }
              {
!                 s_0.f2.f = 1w0;
              }
!             s_0.z = 1w1;
          }
!         f<tuple_0>(s_0.f1);
!         tmp = s_0.f2.f & s_0.z;
          r = tmp;
      }
  }
--- 12,39 ----
  }
  extern void f<D>(in D data);
  control c(inout bit<1> r) {
!     T s_0_f1_field;
!     T s_0_f1_field_0;
!     T s_0_f2;
!     bit<1> s_0_z;
      bit<1> tmp;
      apply {
          {
              {
                  {
!                     s_0_f1_field.f = 1w0;
                  }
                  {
!                     s_0_f1_field_0.f = 1w1;
                  }
              }
              {
!                 s_0_f2.f = 1w0;
              }
!             s_0_z = 1w1;
          }
!         f<tuple_0>({ s_0_f1_field, s_0_f1_field_0 });
!         tmp = s_0_f2.f & s_0_z;
          r = tmp;
      }
  }
