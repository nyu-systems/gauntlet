--- dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:29:28.027115500 +0200
+++ dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:29:28.116736600 +0200
@@ -3,12 +3,6 @@ struct S {
 }
 control c(inout bit<32> b) {
     @name("c.a") action a_0() {
-        {
-        }
-        {
-        }
-        {
-        }
         b = 32w0;
     }
     apply {
