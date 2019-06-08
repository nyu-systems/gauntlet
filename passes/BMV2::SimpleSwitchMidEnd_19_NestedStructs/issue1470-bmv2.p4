--- before_pass
+++ after_pass
@@ -26,24 +26,25 @@ struct headers_t {
     ipv4_h ipv4;
 }
 parser OuterParser(packet_in pkt, out headers_t hdr, inout meta_t m, inout standard_metadata_t meta) {
-    headers_t hdr_1;
+    eth_h hdr_1_eth;
+    ipv4_h hdr_1_ipv4;
     state start {
-        hdr_1.eth.setInvalid();
-        hdr_1.ipv4.setInvalid();
-        pkt.extract<eth_h>(hdr_1.eth);
-        transition select(hdr_1.eth.type) {
+        hdr_1_eth.setInvalid();
+        hdr_1_ipv4.setInvalid();
+        pkt.extract<eth_h>(hdr_1_eth);
+        transition select(hdr_1_eth.type) {
             16w0x800: InnerParser_parse_ipv4;
             default: start_0;
         }
     }
     state InnerParser_parse_ipv4 {
-        pkt.extract<ipv4_h>(hdr_1.ipv4);
+        pkt.extract<ipv4_h>(hdr_1_ipv4);
         transition start_0;
     }
     state start_0 {
         {
-            hdr.eth = hdr_1.eth;
-            hdr.ipv4 = hdr_1.ipv4;
+            hdr.eth = hdr_1_eth;
+            hdr.ipv4 = hdr_1_ipv4;
         }
         transition accept;
     }
