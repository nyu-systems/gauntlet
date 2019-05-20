*** dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:00:36.076396700 +0200
--- dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:36.085836200 +0200
*************** struct metadata_t {
*** 6,12 ****
  }
  control I(inout metadata_t meta) {
      apply {
!         if (meta.foo == { 9w192 }) 
              meta.foo._v = meta.foo._v + 9w1;
      }
  }
--- 6,12 ----
  }
  control I(inout metadata_t meta) {
      apply {
!         if (true && meta.foo._v == 9w192) 
              meta.foo._v = meta.foo._v + 9w1;
      }
  }
