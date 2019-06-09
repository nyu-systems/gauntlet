--- before_pass
+++ after_pass
@@ -80,7 +80,8 @@ struct fwd_metadata_t {
     bit<24> out_bd;
 }
 struct metadata {
-    fwd_metadata_t fwd_metadata;
+    bit<32> _fwd_metadata_l2ptr0;
+    bit<24> _fwd_metadata_out_bd1;
 }
 struct Tcp_option_sack_top {
     bit<8> kind;
@@ -327,7 +328,7 @@ control ingress(inout headers hdr, inout
         }
     }
     @name("ingress.set_l2ptr") action set_l2ptr(bit<32> l2ptr) {
-        meta.fwd_metadata.l2ptr = l2ptr;
+        meta._fwd_metadata_l2ptr0 = l2ptr;
     }
     @name("ingress.ipv4_da_lpm") table ipv4_da_lpm_0 {
         key = {
@@ -340,14 +341,14 @@ control ingress(inout headers hdr, inout
         default_action = my_drop();
     }
     @name("ingress.set_bd_dmac_intf") action set_bd_dmac_intf(bit<24> bd, bit<48> dmac, bit<9> intf) {
-        meta.fwd_metadata.out_bd = bd;
+        meta._fwd_metadata_out_bd1 = bd;
         hdr.ethernet.dstAddr = dmac;
         standard_metadata.egress_spec = intf;
         hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
     }
     @name("ingress.mac_da") table mac_da_0 {
         key = {
-            meta.fwd_metadata.l2ptr: exact @name("meta.fwd_metadata.l2ptr") ;
+            meta._fwd_metadata_l2ptr0: exact @name("meta.fwd_metadata.l2ptr") ;
         }
         actions = {
             set_bd_dmac_intf();
@@ -418,7 +419,7 @@ control egress(inout headers hdr, inout
     }
     @name("egress.send_frame") table send_frame_0 {
         key = {
-            meta.fwd_metadata.out_bd: exact @name("meta.fwd_metadata.out_bd") ;
+            meta._fwd_metadata_out_bd1: exact @name("meta.fwd_metadata.out_bd") ;
         }
         actions = {
             rewrite_mac();
