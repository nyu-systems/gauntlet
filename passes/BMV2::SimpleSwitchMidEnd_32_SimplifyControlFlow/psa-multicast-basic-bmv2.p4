--- before_pass
+++ after_pass
@@ -21,10 +21,8 @@ parser IngressParserImpl(packet_in pkt,
 }
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     @name(".multicast") action multicast() {
-        {
-            ostd.drop = false;
-            ostd.multicast_group = hdr.ethernet.dstAddr[31:0];
-        }
+        ostd.drop = false;
+        ostd.multicast_group = hdr.ethernet.dstAddr[31:0];
     }
     apply {
         multicast();
