--- dumps/p4_16_samples/issue1466.p4/pruned/issue1466-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:16.674984700 +0200
+++ dumps/p4_16_samples/issue1466.p4/pruned/issue1466-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:16.677464500 +0200
@@ -7,7 +7,6 @@ control A(inout hdr _hdr) {
         _hdr_1 = _hdr;
         _hdr_1.g = 1w1;
         _hdr = _hdr_1;
-        _hdr_1 = _hdr;
         _hdr_1.g = 1w1;
         _hdr = _hdr_1;
     }
