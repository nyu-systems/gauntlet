--- dumps/pruned/side_effects-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:33:53.816649000 +0200
+++ dumps/pruned/side_effects-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-06-08 18:33:53.818662300 +0200
@@ -33,7 +33,7 @@ control my() {
         tmp_22 = g(a);
         a = tmp_22;
         tmp_23 = g(a[0:0]);
-        a[0:0] = tmp_23;
+        a = a & ~1w0x1 | (bit<1>)tmp_23 << 0 & 1w0x1;
         g(a);
     }
 }
