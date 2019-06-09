--- before_pass
+++ after_pass
@@ -29,7 +29,6 @@ struct headers {
 struct metadata {
 }
 parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
-    bit<8> my_next_hdr_type_0;
     state start {
         pkt.extract<h1_t>(hdr.h1);
         verify(hdr.h1.hdr_type == 8w1, error.BadHeaderType);
@@ -42,8 +41,7 @@ parser parserI(packet_in pkt, out header
     state parse_first_h2 {
         pkt.extract<h2_t>(hdr.h2.next);
         verify(hdr.h2.last.hdr_type == 8w2, error.BadHeaderType);
-        my_next_hdr_type_0 = hdr.h2.last.next_hdr_type;
-        transition select(my_next_hdr_type_0) {
+        transition select(hdr.h2.last.next_hdr_type) {
             8w2: parse_other_h2;
             8w3: parse_h3;
             default: accept;
