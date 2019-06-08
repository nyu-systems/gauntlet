--- dumps/pruned/newtype-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:33:00.627276200 +0200
+++ dumps/pruned/newtype-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:00.644256800 +0200
@@ -9,13 +9,13 @@ header H {
     N32 field;
 }
 control c(out B32 x) {
-    @name(".NoAction") action NoAction_0() {
-    }
     N32 k;
     bit<32> b_1;
     N32 n_1;
     N32 n1;
     S s;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("c.t") table t {
         actions = {
             NoAction_0();
