--- dumps/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:12.417575100 +0200
+++ dumps/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:12.488012600 +0200
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
