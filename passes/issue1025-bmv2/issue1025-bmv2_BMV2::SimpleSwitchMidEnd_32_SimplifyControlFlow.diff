--- before_pass
+++ after_pass
@@ -61,14 +61,10 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        {
-            tmp_2 = pkt.lookahead<bit<8>>();
-            tmp.setValid();
-            {
-                tmp.version = tmp_2[7:4];
-                tmp.ihl = tmp_2[3:0];
-            }
-        }
+        tmp_2 = pkt.lookahead<bit<8>>();
+        tmp.setValid();
+        tmp.version = tmp_2[7:4];
+        tmp.ihl = tmp_2[3:0];
         pkt.extract<ipv4_t>(hdr.ipv4, (bit<32>)((bit<9>)tmp_2[3:0] << 3));
         transition select(hdr.ipv4.protocol) {
             8w6: parse_tcp;
