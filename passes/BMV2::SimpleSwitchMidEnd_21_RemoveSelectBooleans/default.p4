--- dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 17:29:32.215930100 +0200
+++ dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 17:29:32.221294200 +0200
@@ -7,15 +7,15 @@ parser p0(packet_in p, out Header h) {
     state start {
         b = true;
         p.extract<Header>(h);
-        transition select(h.data, b) {
-            (default, true): next;
+        transition select(h.data, (bit<1>)b) {
+            (default, (bit<1>)true): next;
             (default, default): reject;
         }
     }
     state next {
         p.extract<Header>(h);
-        transition select(h.data, b) {
-            (default, true): accept;
+        transition select(h.data, (bit<1>)b) {
+            (default, (bit<1>)true): accept;
             (default, default): reject;
             default: reject;
         }
