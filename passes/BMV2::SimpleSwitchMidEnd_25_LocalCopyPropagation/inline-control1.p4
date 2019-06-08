--- dumps/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:49.916506100 +0200
+++ dumps/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:49.919150800 +0200
@@ -3,17 +3,12 @@ extern Y {
     bit<32> get();
 }
 control d(out bit<32> x) {
-    bit<32> y;
-    bit<32> x_1;
     bit<32> cinst_tmp_0;
     @name("d.cinst.y") Y(32w16) cinst_y_0;
     apply {
         cinst_tmp_0 = cinst_y_0.get();
-        x_1 = cinst_tmp_0;
-        x = x_1;
+        x = cinst_tmp_0;
         cinst_tmp_0 = cinst_y_0.get();
-        x_1 = cinst_tmp_0;
-        y = x_1;
     }
 }
 control dproto(out bit<32> x);
