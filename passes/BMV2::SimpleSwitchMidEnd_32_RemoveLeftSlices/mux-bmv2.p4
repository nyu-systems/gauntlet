--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-05-20 17:31:24.667941500 +0200
+++ dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-05-20 17:31:24.671583200 +0200
@@ -21,7 +21,7 @@ control Eg(inout Headers hdrs, inout Met
         val = res;
         tmp_0 = res[31:0];
         tmp_0 = tmp_0;
-        val[31:0] = tmp_0;
+        val = val & ~64w0xffffffff | (bit<64>)tmp_0 << 0 & 64w0xffffffff;
         res = val;
     }
     apply {
