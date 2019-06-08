--- dumps/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-06-08 18:32:24.215990500 +0200
+++ dumps/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-06-08 18:32:24.217880400 +0200
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
