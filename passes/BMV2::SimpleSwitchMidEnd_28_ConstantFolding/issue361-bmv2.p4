--- before_pass
+++ after_pass
@@ -10,10 +10,7 @@ struct my_metadata {
 }
 parser MyParser(packet_in b, out my_packet p, inout my_metadata m, inout standard_metadata_t s) {
     state start {
-        transition select((bit<1>)true) {
-            1w0: next;
-            1w1: accept;
-        }
+        transition accept;
     }
     state next {
         b.extract<H>(p.h);
