--- dumps/p4_16_samples/issue1595-1.p4/pruned/issue1595-1-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:30:22.092392800 +0200
+++ dumps/p4_16_samples/issue1595-1.p4/pruned/issue1595-1-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 17:30:22.102213500 +0200
@@ -10,7 +10,7 @@ control c(inout bit<32> b) {
     apply {
         switch (t.apply().action_run) {
             a_0: {
-                b[6:3] = 4w1;
+                b = b & ~32w0x78 | (bit<32>)4w1 << 3 & 32w0x78;
             }
         }
     }
