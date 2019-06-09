--- before_pass
+++ after_pass
@@ -44,11 +44,17 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control ingress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
-    @name(".my_drop") action my_drop(inout standard_metadata_t smeta) {
+    standard_metadata_t smeta;
+    @name(".my_drop") action my_drop() {
+        smeta = standard_metadata;
         mark_to_drop(smeta);
+        standard_metadata = smeta;
     }
-    @name(".my_drop") action my_drop_0(inout standard_metadata_t smeta_1) {
+    standard_metadata_t smeta_1;
+    @name(".my_drop") action my_drop_0() {
+        smeta_1 = standard_metadata;
         mark_to_drop(smeta_1);
+        standard_metadata = smeta_1;
     }
     @name(".NoAction") action NoAction_0() {
     }
@@ -61,16 +67,16 @@ control ingress(inout headers_t hdr, ino
         }
         actions = {
             set_output();
-            my_drop(standard_metadata);
+            my_drop();
         }
-        default_action = my_drop(standard_metadata);
+        default_action = my_drop();
     }
     @name("ingress.ipv4_sa_filter") table ipv4_sa_filter_0 {
         key = {
             hdr.ipv4.srcAddr: ternary @name("hdr.ipv4.srcAddr") ;
         }
         actions = {
-            my_drop_0(standard_metadata);
+            my_drop_0();
             NoAction_0();
         }
         const default_action = NoAction_0();
