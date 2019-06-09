--- before_pass
+++ after_pass
@@ -58,6 +58,7 @@ control ingress(inout headers_t hdr, ino
     bit<8> byte2_0;
     bit<8> byte3_0;
     standard_metadata_t smeta;
+    standard_metadata_t smeta_1;
     @name(".my_drop") action my_drop() {
         {
             smeta.ingress_port = standard_metadata.ingress_port;
@@ -109,7 +110,6 @@ control ingress(inout headers_t hdr, ino
             standard_metadata.priority = smeta.priority;
         }
     }
-    standard_metadata_t smeta_1;
     @name(".my_drop") action my_drop_0() {
         {
             smeta_1.ingress_port = standard_metadata.ingress_port;
@@ -231,9 +231,9 @@ control ingress(inout headers_t hdr, ino
     }
 }
 control egress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
+    standard_metadata_t smeta_2;
     @name(".NoAction") action NoAction_0() {
     }
-    standard_metadata_t smeta_2;
     @name(".my_drop") action my_drop_1() {
         {
             smeta_2.ingress_port = standard_metadata.ingress_port;
