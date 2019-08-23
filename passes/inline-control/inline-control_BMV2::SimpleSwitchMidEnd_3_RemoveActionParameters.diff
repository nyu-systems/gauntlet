--- before_pass
+++ after_pass
@@ -3,8 +3,8 @@ extern Y {
     bit<32> get();
 }
 control d(out bit<32> x) {
-    @name("d.cinst.y") Y(32w16) cinst_y;
     bit<32> cinst_tmp;
+    @name("d.cinst.y") Y(32w16) cinst_y;
     apply {
         cinst_tmp = cinst_y.get();
         x = cinst_tmp;
