--- before_pass
+++ after_pass
@@ -29,14 +29,17 @@ control cEgress(inout Parsed_packet hdr,
     apply {
     }
 }
+struct tuple_0 {
+    bit<16> field;
+}
 control vc(inout Parsed_packet hdr, inout Metadata meta) {
     apply {
-        verify_checksum<tuple<bit<16>>, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
     }
 }
 control uc(inout Parsed_packet hdr, inout Metadata meta) {
     apply {
-        update_checksum<tuple<bit<16>>, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
     }
 }
 V1Switch<Parsed_packet, Metadata>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;
