--- dumps/pruned/issue1595-1-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:32:06.575963600 +0200
+++ dumps/pruned/issue1595-1-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-06-08 18:32:06.577737800 +0200
@@ -10,7 +10,7 @@ control c(inout bit<32> b) {
     apply {
         switch (t.apply().action_run) {
             a_0: {
-                b[6:3] = 4w1;
+                b = b & ~32w0x78 | (bit<32>)4w1 << 3 & 32w0x78;
             }
         }
     }
