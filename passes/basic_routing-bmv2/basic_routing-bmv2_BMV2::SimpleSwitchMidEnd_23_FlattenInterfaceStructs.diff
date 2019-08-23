--- before_pass
+++ after_pass
@@ -25,7 +25,9 @@ header ipv4_t {
     bit<32> dstAddr;
 }
 struct metadata {
-    ingress_metadata_t ingress_metadata;
+    bit<12> _ingress_metadata_vrf0;
+    bit<16> _ingress_metadata_bd1;
+    bit<16> _ingress_metadata_nexthop_index2;
 }
 struct headers {
     ethernet_t ethernet;
@@ -60,7 +62,7 @@ control egress(inout headers hdr, inout
             @defaultonly NoAction_0();
         }
         key = {
-            meta.ingress_metadata.nexthop_index: exact @name("meta.ingress_metadata.nexthop_index") ;
+            meta._ingress_metadata_nexthop_index2: exact @name("meta.ingress_metadata.nexthop_index") ;
         }
         size = 32768;
         default_action = NoAction_0();
@@ -81,7 +83,7 @@ control ingress(inout headers hdr, inout
     @name(".NoAction") action NoAction_11() {
     }
     @name("ingress.set_vrf") action set_vrf(bit<12> vrf) {
-        meta.ingress_metadata.vrf = vrf;
+        meta._ingress_metadata_vrf0 = vrf;
     }
     @name("ingress.on_miss") action on_miss_2() {
     }
@@ -90,18 +92,18 @@ control ingress(inout headers hdr, inout
     @name("ingress.on_miss") action on_miss_6() {
     }
     @name("ingress.fib_hit_nexthop") action fib_hit_nexthop(bit<16> nexthop_index) {
-        meta.ingress_metadata.nexthop_index = nexthop_index;
+        meta._ingress_metadata_nexthop_index2 = nexthop_index;
         hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
     }
     @name("ingress.fib_hit_nexthop") action fib_hit_nexthop_2(bit<16> nexthop_index) {
-        meta.ingress_metadata.nexthop_index = nexthop_index;
+        meta._ingress_metadata_nexthop_index2 = nexthop_index;
         hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
     }
     @name("ingress.set_egress_details") action set_egress_details(bit<9> egress_spec) {
         standard_metadata.egress_spec = egress_spec;
     }
     @name("ingress.set_bd") action set_bd(bit<16> bd) {
-        meta.ingress_metadata.bd = bd;
+        meta._ingress_metadata_bd1 = bd;
     }
     @name("ingress.bd") table bd_0 {
         actions = {
@@ -109,7 +111,7 @@ control ingress(inout headers hdr, inout
             @defaultonly NoAction_1();
         }
         key = {
-            meta.ingress_metadata.bd: exact @name("meta.ingress_metadata.bd") ;
+            meta._ingress_metadata_bd1: exact @name("meta.ingress_metadata.bd") ;
         }
         size = 65536;
         default_action = NoAction_1();
@@ -121,8 +123,8 @@ control ingress(inout headers hdr, inout
             @defaultonly NoAction_8();
         }
         key = {
-            meta.ingress_metadata.vrf: exact @name("meta.ingress_metadata.vrf") ;
-            hdr.ipv4.dstAddr         : exact @name("hdr.ipv4.dstAddr") ;
+            meta._ingress_metadata_vrf0: exact @name("meta.ingress_metadata.vrf") ;
+            hdr.ipv4.dstAddr           : exact @name("hdr.ipv4.dstAddr") ;
         }
         size = 131072;
         default_action = NoAction_8();
@@ -134,8 +136,8 @@ control ingress(inout headers hdr, inout
             @defaultonly NoAction_9();
         }
         key = {
-            meta.ingress_metadata.vrf: exact @name("meta.ingress_metadata.vrf") ;
-            hdr.ipv4.dstAddr         : lpm @name("hdr.ipv4.dstAddr") ;
+            meta._ingress_metadata_vrf0: exact @name("meta.ingress_metadata.vrf") ;
+            hdr.ipv4.dstAddr           : lpm @name("hdr.ipv4.dstAddr") ;
         }
         size = 16384;
         default_action = NoAction_9();
@@ -147,7 +149,7 @@ control ingress(inout headers hdr, inout
             @defaultonly NoAction_10();
         }
         key = {
-            meta.ingress_metadata.nexthop_index: exact @name("meta.ingress_metadata.nexthop_index") ;
+            meta._ingress_metadata_nexthop_index2: exact @name("meta.ingress_metadata.nexthop_index") ;
         }
         size = 32768;
         default_action = NoAction_10();
