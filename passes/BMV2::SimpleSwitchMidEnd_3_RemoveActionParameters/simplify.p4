--- dumps/p4_16_samples/simplify.p4/pruned/simplify-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:32:00.023510800 +0200
+++ dumps/p4_16_samples/simplify.p4/pruned/simplify-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:32:00.045276100 +0200
@@ -1,12 +1,12 @@
 #include <core.p4>
 control c(out bool x) {
+    bool tmp_2;
+    bool tmp_3;
+    bool tmp_4;
     @name(".NoAction") action NoAction_0() {
     }
     @name(".NoAction") action NoAction_3() {
     }
-    bool tmp_2;
-    bool tmp_3;
-    bool tmp_4;
     @name("c.t1") table t1 {
         key = {
             x: exact @name("x") ;
