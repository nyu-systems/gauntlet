*** dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:00:38.330010800 +0200
--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:38.333081500 +0200
*************** control test(out bool zout) {
*** 14,21 ****
      apply {
          p = { 32w4, 32w5 };
          q = { 32w2, 32w3 };
!         zout = p == { 32w4, 32w5 };
!         zout = zout && q == { 32w2, 32w3 };
      }
  }
  top(test()) main;
--- 14,21 ----
      apply {
          p = { 32w4, 32w5 };
          q = { 32w2, 32w3 };
!         zout = true && p.field == 32w4 && p.field_0 == 32w5;
!         zout = zout && (true && q.l == 32w2 && q.r == 32w3);
      }
  }
  top(test()) main;
