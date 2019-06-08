--- before_pass
+++ after_pass
@@ -5,10 +5,7 @@ header Header {
 parser p0(packet_in p, out Header h) {
     state start {
         p.extract<Header>(h);
-        transition select(h.data) {
-            default: next;
-            default: reject;
-        }
+        transition next;
     }
     state next {
         transition accept;
