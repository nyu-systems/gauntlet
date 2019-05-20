--- dumps/p4_16_samples/initializers.p4/pruned/initializers-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:00.706291900 +0200
+++ dumps/p4_16_samples/initializers.p4/pruned/initializers-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:30:00.710301500 +0200
@@ -15,7 +15,7 @@ parser P() {
 control C() {
     @name("C.fake") Fake() fake_2;
     apply {
-        fake_2.call(32w0 + 32w1);
+        fake_2.call(32w1);
     }
 }
 parser SimpleParser();
