--- dumps/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:12.389518200 +0200
+++ dumps/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:12.392084400 +0200
@@ -66,7 +66,10 @@ parser parserI(packet_in pkt, out header
         {
             tmp = pkt.lookahead<bit<8>>();
             tmp_2.setValid();
-            tmp_2 = { tmp[7:4], tmp[3:0] };
+            {
+                tmp_2.version = tmp[7:4];
+                tmp_2.ihl = tmp[3:0];
+            }
         }
         tmp_3 = (bit<9>)tmp_2.ihl << 3;
         tmp_4 = (bit<32>)tmp_3;
