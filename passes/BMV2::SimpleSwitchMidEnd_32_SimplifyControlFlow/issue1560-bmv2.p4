--- before_pass
+++ after_pass
@@ -68,14 +68,10 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        {
-            tmp_4 = pkt.lookahead<bit<8>>();
-            tmp.setValid();
-            {
-                tmp.version = tmp_4[7:4];
-                tmp.ihl = tmp_4[3:0];
-            }
-        }
+        tmp_4 = pkt.lookahead<bit<8>>();
+        tmp.setValid();
+        tmp.version = tmp_4[7:4];
+        tmp.ihl = tmp_4[3:0];
         pkt.extract<ipv4_t>(hdr.ipv4, (bit<32>)(((bit<9>)tmp_4[3:0] << 2) + 9w492 << 3));
         verify(hdr.ipv4.version == 4w4, error.IPv4IncorrectVersion);
         verify(hdr.ipv4.ihl >= 4w5, error.IPv4HeaderTooShort);
@@ -156,10 +152,8 @@ control cIngress(inout headers hdr, inou
         t0_0.apply();
         t1_0.apply();
         meta._hash12 = hdr.ipv4.dstAddr[15:0];
-        {
-            key_0 = hdr.ipv4.dstAddr[15:0];
-            t2_0.apply();
-        }
+        key_0 = hdr.ipv4.dstAddr[15:0];
+        t2_0.apply();
     }
 }
 control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
