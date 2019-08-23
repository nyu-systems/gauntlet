--- before_pass
+++ after_pass
@@ -66,7 +66,10 @@ parser parserI(packet_in pkt, out header
         {
             tmp_2 = pkt.lookahead<bit<8>>();
             tmp.setValid();
-            tmp = IPv4_up_to_ihl_only_h {version = tmp_2[7:4],ihl = tmp_2[3:0]};
+            {
+                tmp.version = tmp_2[7:4];
+                tmp.ihl = tmp_2[3:0];
+            }
         }
         tmp_0 = (bit<9>)tmp.ihl << 3;
         tmp_1 = (bit<32>)tmp_0;
