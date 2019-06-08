--- before_pass
+++ after_pass
@@ -26,8 +26,8 @@ parser p1(packet_in p, out Header h) {
         h.data2 = h.data3 + 32w1;
         stack[1].isValid();
         transition select((bit<1>)h.isValid()) {
-            (bit<1>)true: next1;
-            (bit<1>)false: next2;
+            1w1: next1;
+            1w0: next2;
         }
     }
     state next1 {
