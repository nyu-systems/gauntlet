--- dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:17.411302600 +0200
+++ dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:17.470335600 +0200
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
