--- dumps/p4_16_samples/parser-conditional.p4/pruned/parser-conditional-BMV2::SimpleSwitchMidEnd_20_SimplifySelectList.p4	2019-05-20 17:31:29.856241000 +0200
+++ dumps/p4_16_samples/parser-conditional.p4/pruned/parser-conditional-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 17:31:29.858737600 +0200
@@ -6,9 +6,9 @@ parser p(out bit<32> b) {
     bit<32> tmp_4;
     state start {
         a = 32w1;
-        transition select(a == 32w0) {
-            true: start_true;
-            false: start_false;
+        transition select((bit<1>)(a == 32w0)) {
+            (bit<1>)true: start_true;
+            (bit<1>)false: start_false;
         }
     }
     state start_true {
@@ -22,15 +22,15 @@ parser p(out bit<32> b) {
     state start_join {
         b = tmp_2;
         b = b + 32w1;
-        transition select(a > 32w0) {
-            true: start_true_0;
-            false: start_false_0;
+        transition select((bit<1>)(a > 32w0)) {
+            (bit<1>)true: start_true_0;
+            (bit<1>)false: start_false_0;
         }
     }
     state start_true_0 {
-        transition select(a > 32w1) {
-            true: start_true_0_true;
-            false: start_true_0_false;
+        transition select((bit<1>)(a > 32w1)) {
+            (bit<1>)true: start_true_0_true;
+            (bit<1>)false: start_true_0_false;
         }
     }
     state start_true_0_true {
