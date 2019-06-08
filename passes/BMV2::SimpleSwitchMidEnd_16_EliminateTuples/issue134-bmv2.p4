--- dumps/pruned/issue134-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:31:59.519982200 +0200
+++ dumps/pruned/issue134-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:31:59.522025800 +0200
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
