--- dumps/p4_16_samples/inline-control.p4/pruned/inline-control-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:30:02.137141600 +0200
+++ dumps/p4_16_samples/inline-control.p4/pruned/inline-control-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:30:02.160667900 +0200
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
