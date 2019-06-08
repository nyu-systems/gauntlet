--- dumps/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:05.589358700 +0200
+++ dumps/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:05.632097700 +0200
@@ -71,14 +71,10 @@ parser parserI(packet_in pkt, out header
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
