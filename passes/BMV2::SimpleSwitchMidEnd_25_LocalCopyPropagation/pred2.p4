--- dumps/p4_16_samples/pred2.p4/pruned/pred2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:33.587389200 +0200
+++ dumps/p4_16_samples/pred2.p4/pruned/pred2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:33.590350500 +0200
@@ -5,7 +5,6 @@ package top(empty e);
 control Ing() {
     bool tmp_0;
     @name("Ing.cond") action cond() {
-        tmp_0 = tmp_0;
     }
     @name("Ing.tbl_cond") table tbl_cond {
         actions = {
