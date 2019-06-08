--- dumps/pruned/issue823-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:42.578609900 +0200
+++ dumps/pruned/issue823-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:32:42.586986000 +0200
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
