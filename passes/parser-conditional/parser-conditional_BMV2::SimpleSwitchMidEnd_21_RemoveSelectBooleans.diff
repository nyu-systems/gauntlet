--- before_pass
+++ after_pass
@@ -6,9 +6,9 @@ parser p(out bit<32> b) {
     bit<32> tmp_1;
     state start {
         a_0 = 32w1;
-        transition select(a_0 == 32w0) {
-            true: start_true;
-            false: start_false;
+        transition select((bit<1>)(a_0 == 32w0)) {
+            (bit<1>)true: start_true;
+            (bit<1>)false: start_false;
         }
     }
     state start_true {
@@ -22,15 +22,15 @@ parser p(out bit<32> b) {
     state start_join {
         b = tmp;
         b = b + 32w1;
-        transition select(a_0 > 32w0) {
-            true: start_true_0;
-            false: start_false_0;
+        transition select((bit<1>)(a_0 > 32w0)) {
+            (bit<1>)true: start_true_0;
+            (bit<1>)false: start_false_0;
         }
     }
     state start_true_0 {
-        transition select(a_0 > 32w1) {
-            true: start_true_0_true;
-            false: start_true_0_false;
+        transition select((bit<1>)(a_0 > 32w1)) {
+            (bit<1>)true: start_true_0_true;
+            (bit<1>)false: start_true_0_false;
         }
     }
     state start_true_0_true {
