--- before_pass
+++ after_pass
@@ -6,10 +6,7 @@ parser p(out bit<32> b) {
     bit<32> tmp_1;
     state start {
         a_0 = 32w1;
-        transition select((bit<1>)(32w1 == 32w0)) {
-            1w1: start_true;
-            1w0: start_false;
-        }
+        transition start_false;
     }
     state start_true {
         tmp = 32w2;
