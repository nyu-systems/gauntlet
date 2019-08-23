--- before_pass
+++ after_pass
@@ -9,10 +9,8 @@ struct my_packet {
 struct my_metadata {
 }
 parser MyParser(packet_in b, out my_packet p, inout my_metadata m, inout standard_metadata_t s) {
-    bool bv_0;
     state start {
-        bv_0 = true;
-        transition select((bit<1>)bv_0) {
+        transition select((bit<1>)true) {
             1w0: next;
             1w1: accept;
         }
