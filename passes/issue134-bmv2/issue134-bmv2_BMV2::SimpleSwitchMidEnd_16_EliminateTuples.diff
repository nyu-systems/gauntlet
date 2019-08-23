--- before_pass
+++ after_pass
@@ -31,9 +31,12 @@ control VerifyChecksumI(inout H hdr, ino
     apply {
     }
 }
+struct tuple_0 {
+    bit<1> field;
+}
 control ComputeChecksumI(inout H hdr, inout M meta) {
     apply {
-        update_checksum<tuple<bit<1>>, bit<16>>(hdr.ipv4.ihl == 4w5, { 1w0 }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(hdr.ipv4.ihl == 4w5, { 1w0 }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
     }
 }
 V1Switch<H, M>(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;
