--- before_pass
+++ after_pass
@@ -7,8 +7,8 @@ parser p(out bit<32> b) {
     state start {
         a_0 = 32w1;
         transition select((bit<1>)(a_0 == 32w0)) {
-            (bit<1>)true: start_true;
-            (bit<1>)false: start_false;
+            1w1: start_true;
+            1w0: start_false;
         }
     }
     state start_true {
@@ -23,14 +23,14 @@ parser p(out bit<32> b) {
         b = tmp;
         b = b + 32w1;
         transition select((bit<1>)(a_0 > 32w0)) {
-            (bit<1>)true: start_true_0;
-            (bit<1>)false: start_false_0;
+            1w1: start_true_0;
+            1w0: start_false_0;
         }
     }
     state start_true_0 {
         transition select((bit<1>)(a_0 > 32w1)) {
-            (bit<1>)true: start_true_0_true;
-            (bit<1>)false: start_true_0_false;
+            1w1: start_true_0_true;
+            1w0: start_true_0_false;
         }
     }
     state start_true_0_true {
