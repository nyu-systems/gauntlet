--- before_pass
+++ after_pass
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
