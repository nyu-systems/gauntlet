--- dumps/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:02.644440200 +0200
+++ dumps/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:02.693303700 +0200
@@ -42,10 +42,8 @@ parser OuterParser(packet_in pkt, out he
         transition start_0;
     }
     state start_0 {
-        {
-            hdr.eth = hdr_1_eth;
-            hdr.ipv4 = hdr_1_ipv4;
-        }
+        hdr.eth = hdr_1_eth;
+        hdr.ipv4 = hdr_1_ipv4;
         transition accept;
     }
 }
