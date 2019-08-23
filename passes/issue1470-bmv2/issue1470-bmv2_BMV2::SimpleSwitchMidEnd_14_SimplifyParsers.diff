--- before_pass
+++ after_pass
@@ -29,9 +29,6 @@ parser OuterParser(packet_in pkt, out he
     state start {
         hdr.eth.setInvalid();
         hdr.ipv4.setInvalid();
-        transition InnerParser_start;
-    }
-    state InnerParser_start {
         pkt.extract<eth_h>(hdr.eth);
         transition select(hdr.eth.type) {
             16w0x800: InnerParser_parse_ipv4;
