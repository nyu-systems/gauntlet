--- before_pass
+++ after_pass
@@ -20,9 +20,12 @@ parser parserI(packet_in pkt, out Parsed
         transition accept;
     }
 }
+struct tuple_0 {
+    bit<48> field;
+}
 control cIngress(inout Parsed_packet hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
     apply {
-        digest<tuple<bit<48>>>(32w5, { hdr.ethernet.srcAddr });
+        digest<tuple_0>(32w5, { hdr.ethernet.srcAddr });
         hdr.ethernet.srcAddr = 48w0;
     }
 }
