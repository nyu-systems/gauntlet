--- before_pass
+++ after_pass
@@ -218,11 +218,17 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
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
     @name("ingress.set_l2ptr") action set_l2ptr(bit<32> l2ptr) {
         meta.fwd_metadata.l2ptr = l2ptr;
@@ -233,9 +239,9 @@ control ingress(inout headers hdr, inout
         }
         actions = {
             set_l2ptr();
-            my_drop(standard_metadata);
+            my_drop();
         }
-        default_action = my_drop(standard_metadata);
+        default_action = my_drop();
     }
     @name("ingress.set_bd_dmac_intf") action set_bd_dmac_intf(bit<24> bd, bit<48> dmac, bit<9> intf) {
         meta.fwd_metadata.out_bd = bd;
@@ -249,9 +255,9 @@ control ingress(inout headers hdr, inout
         }
         actions = {
             set_bd_dmac_intf();
-            my_drop_0(standard_metadata);
+            my_drop_0();
         }
-        default_action = my_drop_0(standard_metadata);
+        default_action = my_drop_0();
     }
     apply {
         ipv4_da_lpm_0.apply();
@@ -259,8 +265,11 @@ control ingress(inout headers hdr, inout
     }
 }
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    @name(".my_drop") action my_drop_1(inout standard_metadata_t smeta_2) {
+    standard_metadata_t smeta_2;
+    @name(".my_drop") action my_drop_1() {
+        smeta_2 = standard_metadata;
         mark_to_drop(smeta_2);
+        standard_metadata = smeta_2;
     }
     @name("egress.rewrite_mac") action rewrite_mac(bit<48> smac) {
         hdr.ethernet.srcAddr = smac;
@@ -271,9 +280,9 @@ control egress(inout headers hdr, inout
         }
         actions = {
             rewrite_mac();
-            my_drop_1(standard_metadata);
+            my_drop_1();
         }
-        default_action = my_drop_1(standard_metadata);
+        default_action = my_drop_1();
     }
     apply {
         send_frame_0.apply();
