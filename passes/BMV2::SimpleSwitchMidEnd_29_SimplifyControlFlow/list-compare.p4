--- dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:07.936160000 +0200
+++ dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:07.978031000 +0200
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
