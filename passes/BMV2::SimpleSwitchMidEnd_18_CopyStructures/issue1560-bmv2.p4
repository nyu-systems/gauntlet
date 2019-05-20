--- dumps/p4_16_samples/issue1560-bmv2.p4/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:30:20.345181700 +0200
+++ dumps/p4_16_samples/issue1560-bmv2.p4/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:20.349744700 +0200
@@ -74,7 +74,10 @@ parser parserI(packet_in pkt, out header
         {
             tmp = pkt.lookahead<bit<8>>();
             tmp_4.setValid();
-            tmp_4 = { tmp[7:4], tmp[3:0] };
+            {
+                tmp_4.version = tmp[7:4];
+                tmp_4.ihl = tmp[3:0];
+            }
         }
         tmp_5 = (bit<9>)tmp_4.ihl << 2;
         tmp_6 = tmp_5 + 9w492;
