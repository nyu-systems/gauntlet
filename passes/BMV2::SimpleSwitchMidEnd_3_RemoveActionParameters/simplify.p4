--- before_pass
+++ after_pass
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
