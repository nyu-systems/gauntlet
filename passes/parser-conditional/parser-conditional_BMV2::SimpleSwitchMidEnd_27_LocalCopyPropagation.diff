--- before_pass
+++ after_pass
@@ -6,7 +6,7 @@ parser p(out bit<32> b) {
     bit<32> tmp_1;
     state start {
         a_0 = 32w1;
-        transition select((bit<1>)(a_0 == 32w0)) {
+        transition select((bit<1>)(32w1 == 32w0)) {
             1w1: start_true;
             1w0: start_false;
         }
@@ -21,7 +21,7 @@ parser p(out bit<32> b) {
     }
     state start_join {
         b = tmp;
-        b = b + 32w1;
+        b = tmp + 32w1;
         transition select((bit<1>)(a_0 > 32w0)) {
             1w1: start_true_0;
             1w0: start_false_0;
