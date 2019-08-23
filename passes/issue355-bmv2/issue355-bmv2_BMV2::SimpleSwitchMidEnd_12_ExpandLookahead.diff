--- before_pass
+++ after_pass
@@ -15,8 +15,13 @@ control DeparserI(packet_out packet, in
 }
 parser parserI(packet_in pkt, out H hdr, inout M meta, inout standard_metadata_t stdmeta) {
     ethernet_t tmp;
+    bit<112> tmp_0;
     state start {
-        tmp = pkt.lookahead<ethernet_t>();
+        {
+            tmp_0 = pkt.lookahead<bit<112>>();
+            tmp.setValid();
+            tmp = ethernet_t {dstAddr = tmp_0[111:64],srcAddr = tmp_0[63:16],etherType = tmp_0[15:0]};
+        }
         transition select(tmp.etherType) {
             16w0x1000 &&& 16w0x1000: accept;
         }
