--- before_pass
+++ after_pass
@@ -7,15 +7,15 @@ parser p0(packet_in p, out Header h) {
     state start {
         b = true;
         p.extract<Header>(h);
-        transition select(h.data, b) {
-            (default, true): next;
+        transition select(h.data, (bit<1>)b) {
+            (default, (bit<1>)true): next;
             (default, default): reject;
         }
     }
     state next {
         p.extract<Header>(h);
-        transition select(h.data, b) {
-            (default, true): accept;
+        transition select(h.data, (bit<1>)b) {
+            (default, (bit<1>)true): accept;
             (default, default): reject;
             default: reject;
         }
