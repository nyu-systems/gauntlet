--- before_pass
+++ after_pass
@@ -7,15 +7,15 @@ parser p0(packet_in p, out Header h) {
     state start {
         b_0 = true;
         p.extract<Header>(h);
-        transition select(h.data, b_0) {
-            (default, true): next;
+        transition select(h.data, (bit<1>)b_0) {
+            (default, (bit<1>)true): next;
             (default, default): reject;
         }
     }
     state next {
         p.extract<Header>(h);
-        transition select(h.data, b_0) {
-            (default, true): accept;
+        transition select(h.data, (bit<1>)b_0) {
+            (default, (bit<1>)true): accept;
             (default, default): reject;
             default: reject;
         }
