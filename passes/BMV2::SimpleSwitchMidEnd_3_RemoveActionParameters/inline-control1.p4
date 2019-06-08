--- dumps/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:31:49.929974800 +0200
+++ dumps/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:31:49.949705700 +0200
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
