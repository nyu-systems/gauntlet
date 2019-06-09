--- before_pass
+++ after_pass
@@ -9,13 +9,13 @@ header H {
     N32 field;
 }
 control c(out B32 x) {
-    @name(".NoAction") action NoAction_0() {
-    }
     N32 k_0;
     bit<32> b_0;
     N32 n_0;
     N32 n1_0;
     S s_0;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("c.t") table t_0 {
         actions = {
             NoAction_0();
