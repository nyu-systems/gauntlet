--- before_pass
+++ after_pass
@@ -3,8 +3,8 @@ extern Y {
     bit<32> get();
 }
 control d(out bit<32> x) {
-    @name("d.cinst.y") Y(32w16) cinst_y_0;
     bit<32> cinst_tmp_0;
+    @name("d.cinst.y") Y(32w16) cinst_y_0;
     apply {
         cinst_tmp_0 = cinst_y_0.get();
         x = cinst_tmp_0;
