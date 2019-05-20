*** dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:38.356283500 +0200
--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:38.359954500 +0200
*************** struct tuple_0 {
*** 9,27 ****
      bit<32> field_0;
  }
  control test(out bool zout) {
-     tuple_0 p;
-     S q;
      apply {
          {
-             p.field = 32w4;
-             p.field_0 = 32w5;
          }
          {
-             q.l = 32w2;
-             q.r = 32w3;
          }
!         zout = p.field == 32w4 && p.field_0 == 32w5;
!         zout = zout && (q.l == 32w2 && q.r == 32w3);
      }
  }
  top(test()) main;
--- 9,21 ----
      bit<32> field_0;
  }
  control test(out bool zout) {
      apply {
          {
          }
          {
          }
!         zout = 32w4 == 32w4 && 32w5 == 32w5;
!         zout = 32w4 == 32w4 && 32w5 == 32w5 && (32w2 == 32w2 && 32w3 == 32w3);
      }
  }
  top(test()) main;
