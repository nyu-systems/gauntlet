*** dumps/p4_16_samples/nested-tuple.p4/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:48.962198500 +0200
--- dumps/p4_16_samples/nested-tuple.p4/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:49.015019200 +0200
*************** control c(inout bit<1> r) {
*** 20,38 ****
      T s_f1_field_0;
      T s_f2;
      apply {
!         {
!             {
!                 {
!                     s_f1_field.f = 1w0;
!                 }
!                 {
!                     s_f1_field_0.f = 1w1;
!                 }
!             }
!             {
!                 s_f2.f = 1w0;
!             }
!         }
          f<tuple_1>({ s_f1_field, s_f1_field_0 });
          f<tuple_0>({ { 1w0 }, { 1w1 } });
          r = s_f2.f & 1w1;
--- 20,28 ----
      T s_f1_field_0;
      T s_f2;
      apply {
!         s_f1_field.f = 1w0;
!         s_f1_field_0.f = 1w1;
!         s_f2.f = 1w0;
          f<tuple_1>({ s_f1_field, s_f1_field_0 });
          f<tuple_0>({ { 1w0 }, { 1w1 } });
          r = s_f2.f & 1w1;
