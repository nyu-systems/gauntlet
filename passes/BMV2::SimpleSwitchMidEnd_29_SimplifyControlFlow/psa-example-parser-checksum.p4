--- dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:10.613935900 +0200
+++ dumps/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:10.617034100 +0200
@@ -97,11 +97,7 @@ parser IngressParserImpl(packet_in buffe
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     @name(".ingress_drop") action ingress_drop() {
-        {
-        }
-        {
-            ostd.drop = true;
-        }
+        ostd.drop = true;
     }
     @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts;
     @name("ingress.set_error_idx") action set_error_idx_0(ErrorIndex_t idx) {
