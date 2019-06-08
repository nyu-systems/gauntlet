--- dumps/pruned/issue1466-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:02.155798300 +0200
+++ dumps/pruned/issue1466-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:02.157818200 +0200
@@ -7,7 +7,6 @@ control A(inout hdr _hdr) {
         _hdr_1 = _hdr;
         _hdr_1.g = 1w1;
         _hdr = _hdr_1;
-        _hdr_1 = _hdr;
         _hdr_1.g = 1w1;
         _hdr = _hdr_1;
     }
