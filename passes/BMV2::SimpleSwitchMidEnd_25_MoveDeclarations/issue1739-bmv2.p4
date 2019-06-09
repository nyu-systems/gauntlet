--- before_pass
+++ after_pass
@@ -45,6 +45,7 @@ parser ParserImpl(packet_in packet, out
 }
 control ingress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
     standard_metadata_t smeta;
+    standard_metadata_t smeta_1;
     @name(".my_drop") action my_drop() {
         {
             smeta.ingress_port = standard_metadata.ingress_port;
@@ -96,7 +97,6 @@ control ingress(inout headers_t hdr, ino
             standard_metadata.priority = smeta.priority;
         }
     }
-    standard_metadata_t smeta_1;
     @name(".my_drop") action my_drop_0() {
         {
             smeta_1.ingress_port = standard_metadata.ingress_port;
