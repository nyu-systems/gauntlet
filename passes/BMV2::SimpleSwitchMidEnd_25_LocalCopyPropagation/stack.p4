*** dumps/p4_16_samples/stack.p4/pruned/stack-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:30.000149100 +0200
--- dumps/p4_16_samples/stack.p4/pruned/stack-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:30.002276600 +0200
*************** parser p() {
*** 17,27 ****
  }
  control c() {
      h[4] stack_2;
-     h b_2;
      apply {
          stack_2[3].setValid();
!         b_2 = stack_2[3];
!         stack_2[2] = b_2;
          stack_2.push_front(2);
          stack_2.pop_front(2);
      }
--- 17,25 ----
  }
  control c() {
      h[4] stack_2;
      apply {
          stack_2[3].setValid();
!         stack_2[2] = stack_2[3];
          stack_2.push_front(2);
          stack_2.pop_front(2);
      }
