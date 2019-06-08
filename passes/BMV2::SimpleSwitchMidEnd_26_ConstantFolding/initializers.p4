--- dumps/pruned/initializers-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:48.752521300 +0200
+++ dumps/pruned/initializers-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:48.755011100 +0200
@@ -15,7 +15,7 @@ parser P() {
 control C() {
     @name("C.fake") Fake() fake_2;
     apply {
-        fake_2.call(32w0 + 32w1);
+        fake_2.call(32w1);
     }
 }
 parser SimpleParser();
