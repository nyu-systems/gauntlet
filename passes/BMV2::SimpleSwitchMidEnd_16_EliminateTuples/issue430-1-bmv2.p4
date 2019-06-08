--- dumps/pruned/issue430-1-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:32:27.365649200 +0200
+++ dumps/pruned/issue430-1-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:32:27.367526300 +0200
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
