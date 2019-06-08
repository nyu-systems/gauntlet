--- before_pass
+++ after_pass
@@ -43,15 +43,9 @@ parser parserI(packet_in pkt, out header
     }
     state parse_first_h2 {
         hdr_1 = hdr;
-        transition subParserImpl_start;
-    }
-    state subParserImpl_start {
         pkt.extract<h2_t>(hdr_1.h2.next);
         verify(hdr_1.h2.last.hdr_type == 8w2, error.BadHeaderType);
         ret_next_hdr_type = hdr_1.h2.last.next_hdr_type;
-        transition parse_first_h2_0;
-    }
-    state parse_first_h2_0 {
         hdr = hdr_1;
         my_next_hdr_type = ret_next_hdr_type;
         transition select(my_next_hdr_type) {
