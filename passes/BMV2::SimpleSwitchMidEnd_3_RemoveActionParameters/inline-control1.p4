--- before_pass
+++ after_pass
@@ -5,8 +5,8 @@ extern Y {
 control d(out bit<32> x) {
     bit<32> y;
     bit<32> x_1;
-    @name("d.cinst.y") Y(32w16) cinst_y_0;
     bit<32> cinst_tmp_0;
+    @name("d.cinst.y") Y(32w16) cinst_y_0;
     apply {
         cinst_tmp_0 = cinst_y_0.get();
         x_1 = cinst_tmp_0;
