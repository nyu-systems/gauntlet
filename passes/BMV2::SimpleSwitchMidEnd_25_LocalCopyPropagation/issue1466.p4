*** dumps/p4_16_samples/issue1466.p4/pruned/issue1466-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:46.194754100 +0200
--- dumps/p4_16_samples/issue1466.p4/pruned/issue1466-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:46.197296400 +0200
*************** control A(inout hdr _hdr) {
*** 7,13 ****
          _hdr_1 = _hdr;
          _hdr_1.g = 1w1;
          _hdr = _hdr_1;
-         _hdr_1 = _hdr;
          _hdr_1.g = 1w1;
          _hdr = _hdr_1;
      }
--- 7,12 ----
