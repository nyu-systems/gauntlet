--- dumps/pruned/pred2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:33:07.477202400 +0200
+++ dumps/pruned/pred2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:07.482640800 +0200
@@ -5,7 +5,6 @@ package top(empty e);
 control Ing() {
     bool tmp_0;
     @name("Ing.cond") action cond() {
-        tmp_0 = tmp_0;
     }
     @name("Ing.tbl_cond") table tbl_cond {
         actions = {
