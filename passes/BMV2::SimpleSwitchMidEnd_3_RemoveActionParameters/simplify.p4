--- dumps/pruned/simplify-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:33:54.184613000 +0200
+++ dumps/pruned/simplify-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:54.231825500 +0200
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
