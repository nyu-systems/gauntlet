--- before_pass
+++ after_pass
@@ -44,8 +44,11 @@ parser ParserImpl(packet_in packet, out
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
     @name("ingress.ipv4_da_lpm_stats") direct_counter(CounterType.packets) ipv4_da_lpm_stats_0;
     @name("ingress.set_l2ptr") action set_l2ptr(bit<32> l2ptr) {
@@ -76,12 +79,12 @@ control ingress(inout headers hdr, inout
     @name("ingress.mac_da") table mac_da_0 {
         actions = {
             set_bd_dmac_intf();
-            my_drop(standard_metadata);
+            my_drop();
         }
         key = {
             meta.fwd_metadata.l2ptr: exact @name("meta.fwd_metadata.l2ptr") ;
         }
-        default_action = my_drop(standard_metadata);
+        default_action = my_drop();
     }
     apply {
         ipv4_da_lpm_0.apply();
@@ -89,8 +92,11 @@ control ingress(inout headers hdr, inout
     }
 }
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    @name(".my_drop") action my_drop_0(inout standard_metadata_t smeta_1) {
+    standard_metadata_t smeta_1;
+    @name(".my_drop") action my_drop_0() {
+        smeta_1 = standard_metadata;
         mark_to_drop(smeta_1);
+        standard_metadata = smeta_1;
     }
     @name("egress.rewrite_mac") action rewrite_mac(bit<48> smac) {
         hdr.ethernet.srcAddr = smac;
@@ -98,12 +104,12 @@ control egress(inout headers hdr, inout
     @name("egress.send_frame") table send_frame_0 {
         actions = {
             rewrite_mac();
-            my_drop_0(standard_metadata);
+            my_drop_0();
         }
         key = {
             meta.fwd_metadata.out_bd: exact @name("meta.fwd_metadata.out_bd") ;
         }
-        default_action = my_drop_0(standard_metadata);
+        default_action = my_drop_0();
     }
     apply {
         send_frame_0.apply();
