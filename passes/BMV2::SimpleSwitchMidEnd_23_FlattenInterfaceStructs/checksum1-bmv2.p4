--- before_pass
+++ after_pass
@@ -53,7 +53,8 @@ struct mystruct1_t {
     bit<4> b;
 }
 struct metadata {
-    mystruct1_t mystruct1;
+    bit<4> _mystruct1_a0;
+    bit<4> _mystruct1_b1;
 }
 parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     IPv4_up_to_ihl_only_h tmp;
