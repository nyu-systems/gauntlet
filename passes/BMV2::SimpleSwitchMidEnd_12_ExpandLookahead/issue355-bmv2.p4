--- before_pass
+++ after_pass
@@ -15,8 +15,13 @@ control DeparserI(packet_out packet, in
 }
 parser parserI(packet_in pkt, out H hdr, inout M meta, inout standard_metadata_t stdmeta) {
     ethernet_t tmp_0;
+    bit<112> tmp;
     state start {
-        tmp_0 = pkt.lookahead<ethernet_t>();
+        {
+            tmp = pkt.lookahead<bit<112>>();
+            tmp_0.setValid();
+            tmp_0 = { tmp[111:64], tmp[63:16], tmp[15:0] };
+        }
         transition select(tmp_0.etherType) {
             16w0x1000 &&& 16w0x1000: accept;
         }
