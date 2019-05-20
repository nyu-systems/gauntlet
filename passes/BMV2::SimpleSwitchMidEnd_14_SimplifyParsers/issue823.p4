--- dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:31:07.450581800 +0200
+++ dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:31:07.452880800 +0200
@@ -12,9 +12,6 @@ parser MyP1(packet_in pkt, out headers_t
     headers_t hdr_1;
     state start {
         hdr_1.data.setInvalid();
-        transition MyP2_start;
-    }
-    state MyP2_start {
         transition reject;
     }
 }
