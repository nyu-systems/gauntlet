--- dumps/p4_16_samples/stack.p4/pruned/stack-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:10.158621000 +0200
+++ dumps/p4_16_samples/stack.p4/pruned/stack-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:10.167636700 +0200
@@ -17,11 +17,9 @@ parser p() {
 }
 control c() {
     h[4] stack_2;
-    h b_2;
     apply {
         stack_2[3].setValid();
-        b_2 = stack_2[3];
-        stack_2[2] = b_2;
+        stack_2[2] = stack_2[3];
         stack_2.push_front(2);
         stack_2.pop_front(2);
     }
