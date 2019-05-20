*** dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:38.359954500 +0200
--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:00:38.363536500 +0200
*************** control test(out bool zout) {
*** 14,21 ****
          }
          {
          }
!         zout = 32w4 == 32w4 && 32w5 == 32w5;
!         zout = 32w4 == 32w4 && 32w5 == 32w5 && (32w2 == 32w2 && 32w3 == 32w3);
      }
  }
  top(test()) main;
--- 14,21 ----
          }
          {
          }
!         zout = true;
!         zout = true;
      }
  }
  top(test()) main;
