--- dumps/pruned/default-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-06-08 18:31:30.559523300 +0200
+++ dumps/pruned/default-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-06-08 18:31:30.563548900 +0200
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
