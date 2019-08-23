--- before_pass
+++ after_pass
@@ -6,10 +6,10 @@ extern Virtual {
     bit<16> total();
 }
 control c(inout bit<16> p) {
-    @name(".NoAction") action NoAction_0() {
-    }
     bit<16> local_0;
     bit<16> tmp;
+    @name(".NoAction") action NoAction_0() {
+    }
     @name("c.cntr") Virtual() cntr_0 = {
         bit<16> f(in bit<16> ix) {
             return ix + local_0;
