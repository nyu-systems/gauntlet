--- before_pass
+++ after_pass
@@ -28,7 +28,8 @@ struct fwd_meta_t {
     bit<24> out_bd;
 }
 struct meta_t {
-    fwd_meta_t fwd;
+    bit<32> _fwd_l2ptr0;
+    bit<24> _fwd_out_bd1;
 }
 struct headers_t {
     switch_to_cpu_header_t switch_to_cpu;
@@ -161,7 +162,7 @@ control ingress(inout headers_t hdr, ino
         }
     }
     @name("ingress.set_l2ptr") action set_l2ptr(bit<32> l2ptr) {
-        meta.fwd.l2ptr = l2ptr;
+        meta._fwd_l2ptr0 = l2ptr;
     }
     @name("ingress.set_mcast_grp") action set_mcast_grp(bit<16> mcast_grp) {
         standard_metadata.mcast_grp = mcast_grp;
@@ -172,7 +173,7 @@ control ingress(inout headers_t hdr, ino
     }
     @name("ingress.do_clone_i2e") action do_clone_i2e(bit<32> l2ptr) {
         clone3<tuple_0>(CloneType.I2E, 32w5, {  });
-        meta.fwd.l2ptr = l2ptr;
+        meta._fwd_l2ptr0 = l2ptr;
     }
     @name("ingress.ipv4_da_lpm") table ipv4_da_lpm_0 {
         key = {
@@ -188,14 +189,14 @@ control ingress(inout headers_t hdr, ino
         default_action = my_drop();
     }
     @name("ingress.set_bd_dmac_intf") action set_bd_dmac_intf(bit<24> bd, bit<48> dmac, bit<9> intf) {
-        meta.fwd.out_bd = bd;
+        meta._fwd_out_bd1 = bd;
         hdr.ethernet.dstAddr = dmac;
         standard_metadata.egress_spec = intf;
         hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
     }
     @name("ingress.mac_da") table mac_da_0 {
         key = {
-            meta.fwd.l2ptr: exact @name("meta.fwd.l2ptr") ;
+            meta._fwd_l2ptr0: exact @name("meta.fwd.l2ptr") ;
         }
         actions = {
             set_bd_dmac_intf();
@@ -211,7 +212,7 @@ control ingress(inout headers_t hdr, ino
             byte3_0 = 8w2;
             ipv4_address_0 = byte0_0 ++ byte1_0 ++ byte2_0 ++ byte3_0;
             hdr.ipv4.srcAddr = ipv4_address_0;
-            meta.fwd.l2ptr = 32w0xe50b;
+            meta._fwd_l2ptr0 = 32w0xe50b;
         }
         else 
             if (standard_metadata.instance_type == 32w4) {
@@ -221,11 +222,11 @@ control ingress(inout headers_t hdr, ino
                 byte3_0 = 8w99;
                 ipv4_address_0 = byte0_0 ++ byte1_0 ++ byte2_0 ++ byte3_0;
                 hdr.ipv4.srcAddr = ipv4_address_0;
-                meta.fwd.l2ptr = 32w0xec1c;
+                meta._fwd_l2ptr0 = 32w0xec1c;
             }
             else 
                 ipv4_da_lpm_0.apply();
-        if (meta.fwd.l2ptr != 32w0) 
+        if (meta._fwd_l2ptr0 != 32w0) 
             mac_da_0.apply();
     }
 }
@@ -285,7 +286,7 @@ control egress(inout headers_t hdr, inou
         }
     }
     @name("egress.set_out_bd") action set_out_bd(bit<24> bd) {
-        meta.fwd.out_bd = bd;
+        meta._fwd_out_bd1 = bd;
     }
     @name("egress.get_multicast_copy_out_bd") table get_multicast_copy_out_bd_0 {
         key = {
@@ -311,7 +312,7 @@ control egress(inout headers_t hdr, inou
     }
     @name("egress.send_frame") table send_frame_0 {
         key = {
-            meta.fwd.out_bd: exact @name("meta.fwd.out_bd") ;
+            meta._fwd_out_bd1: exact @name("meta.fwd.out_bd") ;
         }
         actions = {
             rewrite_mac();
