--- dumps/pruned/functors3-BMV2::SimpleSwitchMidEnd_9_ConstantFolding.p4	2019-06-08 18:31:42.055987400 +0200
+++ dumps/pruned/functors3-BMV2::SimpleSwitchMidEnd_10_StrengthReduction.p4	2019-06-08 18:31:41.972785600 +0200
@@ -12,7 +12,7 @@ parser p_0(out bit<1> z) {
     }
     state start_0 {
         z = z1;
-        z = z & 1w0 & 1w1;
+        z = 1w0;
         transition accept;
     }
 }
