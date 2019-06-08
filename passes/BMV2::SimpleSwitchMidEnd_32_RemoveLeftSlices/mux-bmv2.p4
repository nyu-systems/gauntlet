--- dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:32:58.189269500 +0200
+++ dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-06-08 18:32:58.193373600 +0200
@@ -21,7 +21,7 @@ control Eg(inout Headers hdrs, inout Met
         val = res;
         tmp_0 = res[31:0];
         tmp_0 = tmp_0;
-        val[31:0] = tmp_0;
+        val = val & ~64w0xffffffff | (bit<64>)tmp_0 << 0 & 64w0xffffffff;
         res = val;
     }
     apply {
