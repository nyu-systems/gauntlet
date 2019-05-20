--- dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 17:30:44.721345300 +0200
+++ dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 17:30:44.734200600 +0200
@@ -12,9 +12,9 @@ parser MyParser(packet_in b, out my_pack
     bool bv;
     state start {
         bv = true;
-        transition select(bv) {
-            false: next;
-            true: accept;
+        transition select((bit<1>)bv) {
+            (bit<1>)false: next;
+            (bit<1>)true: accept;
         }
     }
     state next {
