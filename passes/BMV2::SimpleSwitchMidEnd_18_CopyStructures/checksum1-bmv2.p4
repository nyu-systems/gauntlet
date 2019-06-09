--- before_pass
+++ after_pass
@@ -73,7 +73,10 @@ parser parserI(packet_in pkt, out header
         {
             tmp_4 = pkt.lookahead<bit<8>>();
             tmp.setValid();
-            tmp = {tmp_4[7:4],tmp_4[3:0]};
+            {
+                tmp.version = tmp_4[7:4];
+                tmp.ihl = tmp_4[3:0];
+            }
         }
         tmp_0 = (bit<9>)tmp.ihl << 2;
         tmp_1 = tmp_0 + 9w492;
