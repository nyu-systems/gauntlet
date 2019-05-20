--- dumps/p4_16_samples/functors3.p4/pruned/functors3-BMV2::SimpleSwitchMidEnd_9_ConstantFolding.p4	2019-05-20 17:29:50.078483400 +0200
+++ dumps/p4_16_samples/functors3.p4/pruned/functors3-BMV2::SimpleSwitchMidEnd_10_StrengthReduction.p4	2019-05-20 17:29:49.970504100 +0200
@@ -12,7 +12,7 @@ parser p_0(out bit<1> z) {
     }
     state start_0 {
         z = z1;
-        z = z & 1w0 & 1w1;
+        z = 1w0;
         transition accept;
     }
 }
