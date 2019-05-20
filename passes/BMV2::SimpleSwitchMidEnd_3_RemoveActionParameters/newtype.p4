--- dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:31:27.122428100 +0200
+++ dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:31:27.147149400 +0200
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
