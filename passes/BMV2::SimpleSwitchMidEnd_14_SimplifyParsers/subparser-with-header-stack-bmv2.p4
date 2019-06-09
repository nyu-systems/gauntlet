--- before_pass
+++ after_pass
@@ -40,15 +40,9 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_first_h2 {
-        transition subParserImpl_start;
-    }
-    state subParserImpl_start {
         pkt.extract<h2_t>(hdr.h2.next);
         verify(hdr.h2.last.hdr_type == 8w2, error.BadHeaderType);
         my_next_hdr_type_0 = hdr.h2.last.next_hdr_type;
-        transition parse_first_h2_0;
-    }
-    state parse_first_h2_0 {
         transition select(my_next_hdr_type_0) {
             8w2: parse_other_h2;
             8w3: parse_h3;
