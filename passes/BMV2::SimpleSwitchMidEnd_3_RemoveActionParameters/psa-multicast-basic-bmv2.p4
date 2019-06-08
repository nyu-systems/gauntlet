--- dumps/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:33:24.377728900 +0200
+++ dumps/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:24.415700300 +0200
@@ -20,12 +20,17 @@ parser IngressParserImpl(packet_in pkt,
     }
 }
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    @name(".multicast") action multicast(inout psa_ingress_output_metadata_t meta_1, in MulticastGroup_t multicast_group_1) {
+    psa_ingress_output_metadata_t meta_1;
+    MulticastGroup_t multicast_group_1;
+    @name(".multicast") action multicast() {
+        meta_1 = ostd;
+        multicast_group_1 = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
         meta_1.drop = false;
         meta_1.multicast_group = multicast_group_1;
+        ostd = meta_1;
     }
     apply {
-        multicast(ostd, (MulticastGroup_t)hdr.ethernet.dstAddr[31:0]);
+        multicast();
     }
 }
 parser EgressParserImpl(packet_in buffer, out headers_t hdr, inout metadata_t user_meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
