--- before_pass
+++ after_pass
@@ -49,17 +49,23 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control ingress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
-    @name(".my_drop") action my_drop(inout standard_metadata_t smeta) {
-        mark_to_drop(smeta);
-    }
-    @name(".my_drop") action my_drop_0(inout standard_metadata_t smeta_1) {
-        mark_to_drop(smeta_1);
-    }
     bit<32> ipv4_address_0;
     bit<8> byte0_0;
     bit<8> byte1_0;
     bit<8> byte2_0;
     bit<8> byte3_0;
+    standard_metadata_t smeta;
+    @name(".my_drop") action my_drop() {
+        smeta = standard_metadata;
+        mark_to_drop(smeta);
+        standard_metadata = smeta;
+    }
+    standard_metadata_t smeta_1;
+    @name(".my_drop") action my_drop_0() {
+        smeta_1 = standard_metadata;
+        mark_to_drop(smeta_1);
+        standard_metadata = smeta_1;
+    }
     @name("ingress.set_l2ptr") action set_l2ptr(bit<32> l2ptr) {
         meta.fwd.l2ptr = l2ptr;
     }
@@ -83,9 +89,9 @@ control ingress(inout headers_t hdr, ino
             set_mcast_grp();
             do_resubmit();
             do_clone_i2e();
-            my_drop(standard_metadata);
+            my_drop();
         }
-        default_action = my_drop(standard_metadata);
+        default_action = my_drop();
     }
     @name("ingress.set_bd_dmac_intf") action set_bd_dmac_intf(bit<24> bd, bit<48> dmac, bit<9> intf) {
         meta.fwd.out_bd = bd;
@@ -99,9 +105,9 @@ control ingress(inout headers_t hdr, ino
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
         if (standard_metadata.instance_type == 32w6) {
@@ -132,8 +138,11 @@ control ingress(inout headers_t hdr, ino
 control egress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
     @name(".NoAction") action NoAction_0() {
     }
-    @name(".my_drop") action my_drop_1(inout standard_metadata_t smeta_2) {
+    standard_metadata_t smeta_2;
+    @name(".my_drop") action my_drop_1() {
+        smeta_2 = standard_metadata;
         mark_to_drop(smeta_2);
+        standard_metadata = smeta_2;
     }
     @name("egress.set_out_bd") action set_out_bd(bit<24> bd) {
         meta.fwd.out_bd = bd;
@@ -168,9 +177,9 @@ control egress(inout headers_t hdr, inou
             rewrite_mac();
             do_recirculate();
             do_clone_e2e();
-            my_drop_1(standard_metadata);
+            my_drop_1();
         }
-        default_action = my_drop_1(standard_metadata);
+        default_action = my_drop_1();
     }
     apply {
         if (standard_metadata.instance_type == 32w1) {
