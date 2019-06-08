--- dumps/pruned/newtype1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:00.944965700 +0200
+++ dumps/pruned/newtype1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:33:00.947635700 +0200
@@ -4,7 +4,7 @@ typedef bit<32> Wide_t;
 typedef Wide_t Wide;
 control c(out bool b) {
     apply {
-        b = (Narrow_t)(Wide_t)32w3 == 9w10;
+        b = false;
     }
 }
 control ctrl(out bool b);
