--- before_pass
+++ after_pass
@@ -63,14 +63,10 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        {
-            tmp = pkt.lookahead<bit<8>>();
-            tmp_2.setValid();
-            {
-                tmp_2.version = tmp[7:4];
-                tmp_2.ihl = tmp[3:0];
-            }
-        }
+        tmp = pkt.lookahead<bit<8>>();
+        tmp_2.setValid();
+        tmp_2.version = tmp[7:4];
+        tmp_2.ihl = tmp[3:0];
         tmp_3 = (bit<9>)tmp_2.ihl << 3;
         tmp_4 = (bit<32>)tmp_3;
         pkt.extract<ipv4_t>(hdr.ipv4, tmp_4);
