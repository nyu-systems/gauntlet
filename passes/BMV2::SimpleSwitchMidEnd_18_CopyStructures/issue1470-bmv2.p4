--- dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:30:17.372117200 +0200
+++ dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:17.380048700 +0200
@@ -41,7 +41,10 @@ parser OuterParser(packet_in pkt, out he
         transition start_0;
     }
     state start_0 {
-        hdr = hdr_1;
+        {
+            hdr.eth = hdr_1.eth;
+            hdr.ipv4 = hdr_1.ipv4;
+        }
         transition accept;
     }
 }
