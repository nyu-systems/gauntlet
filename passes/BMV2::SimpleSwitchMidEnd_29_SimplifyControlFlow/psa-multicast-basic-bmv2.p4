--- dumps/p4_16_samples/psa-multicast-basic-bmv2.p4/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:31:51.136343800 +0200
+++ dumps/p4_16_samples/psa-multicast-basic-bmv2.p4/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:31:51.140343500 +0200
@@ -21,12 +21,8 @@ parser IngressParserImpl(packet_in pkt,
 }
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     @name(".multicast") action multicast() {
-        {
-        }
-        {
-            ostd.drop = false;
-            ostd.multicast_group = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
-        }
+        ostd.drop = false;
+        ostd.multicast_group = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
     }
     apply {
         multicast();
