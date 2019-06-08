--- before_pass
+++ after_pass
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
