--- dumps/pruned/nested_select-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-06-08 18:33:00.305521600 +0200
+++ dumps/pruned/nested_select-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-06-08 18:33:00.307552700 +0200
@@ -3,9 +3,9 @@ parser p() {
     bit<8> x;
     state start {
         x = 8w5;
-        transition select(x, x, { x, x }, x) {
-            (8w0, 8w0, { 8w0, 8w0 }, 8w0): accept;
-            (8w1, 8w1, default, 8w1): accept;
+        transition select(x, x, x, x, x) {
+            (8w0, 8w0, 8w0, 8w0, 8w0): accept;
+            (8w1, 8w1, default, default, 8w1): accept;
             default: reject;
         }
     }
