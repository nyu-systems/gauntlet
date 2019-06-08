--- dumps/pruned/slice-def-use1-BMV2::SimpleSwitchMidEnd_31_TableHit.p4	2019-06-08 18:33:55.212627500 +0200
+++ dumps/pruned/slice-def-use1-BMV2::SimpleSwitchMidEnd_32_RemoveLeftSlices.p4	2019-06-08 18:33:55.214640500 +0200
@@ -37,7 +37,7 @@ control Ing(inout Headers headers, inout
     @name("Ing.debug") register<bit<8>>(32w2) debug;
     @name("Ing.act") action act_0() {
         n = 8w0b11111111;
-        n[7:4] = 4w0;
+        n = n & ~8w0xf0 | (bit<8>)4w0 << 4 & 8w0xf0;
         debug.write(32w1, n);
         standard_meta.egress_spec = 9w0;
     }
