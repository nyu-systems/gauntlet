--- before_pass
+++ after_pass
@@ -17,15 +17,11 @@ parser parserI(packet_in pkt, out H hdr,
     ethernet_t tmp;
     bit<112> tmp_0;
     state start {
-        {
-            tmp_0 = pkt.lookahead<bit<112>>();
-            tmp.setValid();
-            {
-                tmp.dstAddr = tmp_0[111:64];
-                tmp.srcAddr = tmp_0[63:16];
-                tmp.etherType = tmp_0[15:0];
-            }
-        }
+        tmp_0 = pkt.lookahead<bit<112>>();
+        tmp.setValid();
+        tmp.dstAddr = tmp_0[111:64];
+        tmp.srcAddr = tmp_0[63:16];
+        tmp.etherType = tmp_0[15:0];
         transition select(tmp_0[15:0]) {
             16w0x1000 &&& 16w0x1000: accept;
         }
