--- dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:27.368473900 +0200
+++ dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:31:27.370259600 +0200
@@ -4,7 +4,7 @@ typedef bit<32> Wide_t;
 typedef Wide_t Wide;
 control c(out bool b) {
     apply {
-        b = (Narrow_t)(Wide_t)32w3 == 9w10;
+        b = false;
     }
 }
 control ctrl(out bool b);
