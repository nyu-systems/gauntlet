--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:19.164242400 +0200
+++ dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:19.259671300 +0200
@@ -10,10 +10,6 @@ struct tuple_0 {
 }
 control test(out bool zout) {
     apply {
-        {
-        }
-        {
-        }
         zout = true;
         zout = true;
     }
