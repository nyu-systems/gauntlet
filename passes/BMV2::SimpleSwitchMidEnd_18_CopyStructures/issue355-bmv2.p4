--- dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:30:43.780543500 +0200
+++ dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:43.783679600 +0200
@@ -20,7 +20,11 @@ parser parserI(packet_in pkt, out H hdr,
         {
             tmp = pkt.lookahead<bit<112>>();
             tmp_0.setValid();
-            tmp_0 = { tmp[111:64], tmp[63:16], tmp[15:0] };
+            {
+                tmp_0.dstAddr = tmp[111:64];
+                tmp_0.srcAddr = tmp[63:16];
+                tmp_0.etherType = tmp[15:0];
+            }
         }
         transition select(tmp_0.etherType) {
             16w0x1000 &&& 16w0x1000: accept;
