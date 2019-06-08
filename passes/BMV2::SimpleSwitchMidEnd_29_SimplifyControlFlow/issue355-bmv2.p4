--- before_pass
+++ after_pass
@@ -17,15 +17,11 @@ parser parserI(packet_in pkt, out H hdr,
     ethernet_t tmp_0;
     bit<112> tmp;
     state start {
-        {
-            tmp = pkt.lookahead<bit<112>>();
-            tmp_0.setValid();
-            {
-                tmp_0.dstAddr = tmp[111:64];
-                tmp_0.srcAddr = tmp[63:16];
-                tmp_0.etherType = tmp[15:0];
-            }
-        }
+        tmp = pkt.lookahead<bit<112>>();
+        tmp_0.setValid();
+        tmp_0.dstAddr = tmp[111:64];
+        tmp_0.srcAddr = tmp[63:16];
+        tmp_0.etherType = tmp[15:0];
         transition select(tmp_0.etherType) {
             16w0x1000 &&& 16w0x1000: accept;
         }
