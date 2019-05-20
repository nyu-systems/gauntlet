*** dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:00:36.122207100 +0200
--- dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:36.125866100 +0200
*************** struct metadata_t {
*** 6,12 ****
  }
  control I(inout metadata_t meta) {
      apply {
!         if (true && meta.foo._v == 9w192) 
              meta.foo._v = meta.foo._v + 9w1;
      }
  }
--- 6,12 ----
  }
  control I(inout metadata_t meta) {
      apply {
!         if (meta.foo._v == 9w192) 
              meta.foo._v = meta.foo._v + 9w1;
      }
  }
