--- dumps/p4_16_samples/parser-conditional.p4/pruned/parser-conditional-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:31:29.865691500 +0200
+++ dumps/p4_16_samples/parser-conditional.p4/pruned/parser-conditional-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:29.870335000 +0200
@@ -7,8 +7,8 @@ parser p(out bit<32> b) {
     state start {
         a = 32w1;
         transition select((bit<1>)(a == 32w0)) {
-            (bit<1>)true: start_true;
-            (bit<1>)false: start_false;
+            1w1: start_true;
+            1w0: start_false;
         }
     }
     state start_true {
@@ -23,14 +23,14 @@ parser p(out bit<32> b) {
         b = tmp_2;
         b = b + 32w1;
         transition select((bit<1>)(a > 32w0)) {
-            (bit<1>)true: start_true_0;
-            (bit<1>)false: start_false_0;
+            1w1: start_true_0;
+            1w0: start_false_0;
         }
     }
     state start_true_0 {
         transition select((bit<1>)(a > 32w1)) {
-            (bit<1>)true: start_true_0_true;
-            (bit<1>)false: start_true_0_false;
+            1w1: start_true_0_true;
+            1w0: start_true_0_false;
         }
     }
     state start_true_0_true {
