--- before_pass
+++ after_pass
@@ -8,14 +8,14 @@ parser p0(packet_in p, out Header h) {
         b_0 = true;
         p.extract<Header>(h);
         transition select(h.data, (bit<1>)b_0) {
-            (default, (bit<1>)true): next;
+            (default, 1w1): next;
             (default, default): reject;
         }
     }
     state next {
         p.extract<Header>(h);
         transition select(h.data, (bit<1>)b_0) {
-            (default, (bit<1>)true): accept;
+            (default, 1w1): accept;
             (default, default): reject;
             default: reject;
         }
