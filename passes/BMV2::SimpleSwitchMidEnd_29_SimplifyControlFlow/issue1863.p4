--- dumps/pruned/issue1863-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:16.009686900 +0200
+++ dumps/pruned/issue1863-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:16.011685400 +0200
@@ -4,10 +4,6 @@ struct S {
 }
 control c(out bit<1> b) {
     apply {
-        {
-        }
-        {
-        }
         b = 1w1;
     }
 }
