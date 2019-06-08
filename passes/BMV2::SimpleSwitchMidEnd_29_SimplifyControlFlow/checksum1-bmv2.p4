--- before_pass
+++ after_pass
@@ -70,14 +70,10 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        {
-            tmp = pkt.lookahead<bit<8>>();
-            tmp_4.setValid();
-            {
-                tmp_4.version = tmp[7:4];
-                tmp_4.ihl = tmp[3:0];
-            }
-        }
+        tmp = pkt.lookahead<bit<8>>();
+        tmp_4.setValid();
+        tmp_4.version = tmp[7:4];
+        tmp_4.ihl = tmp[3:0];
         tmp_5 = (bit<9>)tmp_4.ihl << 2;
         tmp_6 = tmp_5 + 9w492;
         tmp_7 = tmp_6 << 3;
