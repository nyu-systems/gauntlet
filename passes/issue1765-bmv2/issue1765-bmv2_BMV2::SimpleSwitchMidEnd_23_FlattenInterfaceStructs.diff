--- before_pass
+++ after_pass
@@ -53,8 +53,9 @@ struct mystruct1_t {
     bit<4> b;
 }
 struct metadata {
-    mystruct1_t mystruct1;
-    bool        b;
+    bit<4> _mystruct1_a0;
+    bit<4> _mystruct1_b1;
+    bool   _b2;
 }
 parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     IPv4_up_to_ihl_only_h tmp;
@@ -140,7 +141,7 @@ control vc(inout headers hdr, inout meta
 }
 control uc(inout headers hdr, inout metadata meta) {
     apply {
-        update_checksum<tuple_0, bit<16>>(meta.b, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, meta.mystruct1.a ++ meta.mystruct1.b, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.options }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(meta._b2, { hdr.ipv4.version, hdr.ipv4.ihl, hdr.ipv4.diffserv, hdr.ipv4.totalLen, hdr.ipv4.identification, hdr.ipv4.flags, hdr.ipv4.fragOffset, meta._mystruct1_a0 ++ meta._mystruct1_b1, hdr.ipv4.protocol, hdr.ipv4.srcAddr, hdr.ipv4.dstAddr, hdr.ipv4.options }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
     }
 }
 control DeparserI(packet_out packet, in headers hdr) {
