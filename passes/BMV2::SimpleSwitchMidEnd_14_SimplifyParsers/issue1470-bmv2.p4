--- before_pass
+++ after_pass
@@ -30,9 +30,6 @@ parser OuterParser(packet_in pkt, out he
     state start {
         hdr_1.eth.setInvalid();
         hdr_1.ipv4.setInvalid();
-        transition InnerParser_start;
-    }
-    state InnerParser_start {
         pkt.extract<eth_h>(hdr_1.eth);
         transition select(hdr_1.eth.type) {
             16w0x800: InnerParser_parse_ipv4;
