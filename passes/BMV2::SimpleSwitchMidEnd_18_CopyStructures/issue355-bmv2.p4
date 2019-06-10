--- before_pass
+++ after_pass
@@ -20,7 +20,11 @@ parser parserI(packet_in pkt, out H hdr,
         {
             tmp_0 = pkt.lookahead<bit<112>>();
             tmp.setValid();
-            tmp = ethernet_t {dstAddr = tmp_0[111:64],srcAddr = tmp_0[63:16],etherType = tmp_0[15:0]};
+            {
+                tmp.dstAddr = tmp_0[111:64];
+                tmp.srcAddr = tmp_0[63:16];
+                tmp.etherType = tmp_0[15:0];
+            }
         }
         transition select(tmp.etherType) {
             16w0x1000 &&& 16w0x1000: accept;
