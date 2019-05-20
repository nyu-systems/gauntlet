--- dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:33.800779700 +0200
+++ dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:33.803327700 +0200
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
