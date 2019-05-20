--- dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:31:07.463559500 +0200
+++ dumps/p4_16_samples/issue823.p4/pruned/issue823-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 17:31:07.568788700 +0200
@@ -9,9 +9,9 @@ struct headers_t {
     data_h data;
 }
 parser MyP1(packet_in pkt, out headers_t hdr) {
-    headers_t hdr_1;
+    data_h hdr_1_data;
     state start {
-        hdr_1.data.setInvalid();
+        hdr_1_data.setInvalid();
         transition reject;
     }
 }
