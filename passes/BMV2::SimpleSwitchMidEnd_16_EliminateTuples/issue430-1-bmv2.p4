--- dumps/p4_16_samples/issue430-1-bmv2.p4/pruned/issue430-1-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:30:48.529587400 +0200
+++ dumps/p4_16_samples/issue430-1-bmv2.p4/pruned/issue430-1-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:30:48.533438500 +0200
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
