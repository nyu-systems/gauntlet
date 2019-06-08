--- dumps/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:33:24.458431600 +0200
+++ dumps/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:33:24.460515300 +0200
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
