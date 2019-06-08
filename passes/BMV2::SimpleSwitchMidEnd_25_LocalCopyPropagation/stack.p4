--- before_pass
+++ after_pass
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
