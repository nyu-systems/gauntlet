--- before_pass
+++ after_pass
@@ -7,7 +7,7 @@ parser p0(packet_in p, out Header h) {
     state start {
         b_0 = true;
         p.extract<Header>(h);
-        transition select(h.data, (bit<1>)true) {
+        transition select(h.data, 1w1) {
             (default, 1w1): next;
             (default, default): reject;
         }
