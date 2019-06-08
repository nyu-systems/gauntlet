--- dumps/pruned/copy-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:28.712227800 +0200
+++ dumps/pruned/copy-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:28.753046400 +0200
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
