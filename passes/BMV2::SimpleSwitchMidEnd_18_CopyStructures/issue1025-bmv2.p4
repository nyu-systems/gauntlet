--- before_pass
+++ after_pass
@@ -66,7 +66,10 @@ parser parserI(packet_in pkt, out header
         {
             tmp = pkt.lookahead<bit<8>>();
             tmp_2.setValid();
-            tmp_2 = { tmp[7:4], tmp[3:0] };
+            {
+                tmp_2.version = tmp[7:4];
+                tmp_2.ihl = tmp[3:0];
+            }
         }
         tmp_3 = (bit<9>)tmp_2.ihl << 3;
         tmp_4 = (bit<32>)tmp_3;
