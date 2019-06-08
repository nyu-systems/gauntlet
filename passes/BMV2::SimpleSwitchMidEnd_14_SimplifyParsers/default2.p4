--- before_pass
+++ after_pass
@@ -5,9 +5,6 @@ header Header {
 parser p0(packet_in p, out Header h) {
     state start {
         p.extract<Header>(h);
-        transition next;
-    }
-    state next {
         transition accept;
     }
 }
