--- dumps/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:02.611571300 +0200
+++ dumps/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:02.614258000 +0200
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
