--- dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:27.366748100 +0200
+++ dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:27.368473900 +0200
@@ -3,12 +3,8 @@ typedef Narrow_t Narrow;
 typedef bit<32> Wide_t;
 typedef Wide_t Wide;
 control c(out bool b) {
-    Wide x;
-    Narrow y;
     apply {
-        x = 32w3;
-        y = (Narrow_t)(Wide_t)x;
-        b = y == 9w10;
+        b = (Narrow_t)(Wide_t)32w3 == 9w10;
     }
 }
 control ctrl(out bool b);
