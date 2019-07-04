--- before_pass
+++ after_pass
@@ -25,7 +25,7 @@ control cIngress(inout headers_t hdr, in
         meta_1.multicast_group = multicast_group_1;
     }
     apply {
-        multicast(ostd, (MulticastGroup_t)(MulticastGroupUint_t)hdr.ethernet.dstAddr);
+        multicast(ostd, (MulticastGroupUint_t)hdr.ethernet.dstAddr);
     }
 }
 parser EgressParserImpl(packet_in buffer, out headers_t hdr, inout metadata_t user_meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
