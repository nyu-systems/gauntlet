--- dumps/p4_16_samples/side_effects.p4/pruned/side_effects-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:31:59.650869300 +0200
+++ dumps/p4_16_samples/side_effects.p4/pruned/side_effects-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 17:31:59.653941900 +0200
@@ -33,7 +33,7 @@ control my() {
         tmp_22 = g(a);
         a = tmp_22;
         tmp_23 = g(a[0:0]);
-        a[0:0] = tmp_23;
+        a = a & ~1w0x1 | (bit<1>)tmp_23 << 0 & 1w0x1;
         g(a);
     }
 }
