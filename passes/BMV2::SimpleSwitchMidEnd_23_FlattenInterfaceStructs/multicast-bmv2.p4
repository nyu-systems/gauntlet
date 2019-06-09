--- before_pass
+++ after_pass
@@ -23,8 +23,7 @@ header ipv4_t {
     bit<32> dstAddr;
 }
 struct metadata {
-    @name("routing_metadata") 
-    routing_metadata_t routing_metadata;
+    bit<32> _routing_metadata_nhop_ipv40;
 }
 struct headers {
     @name("ethernet") 
@@ -93,7 +92,7 @@ control ingress(inout headers hdr, inout
         mark_to_drop(standard_metadata);
     }
     @name(".set_nhop") action set_nhop(bit<32> nhop_ipv4, bit<9> port) {
-        meta.routing_metadata.nhop_ipv4 = nhop_ipv4;
+        meta._routing_metadata_nhop_ipv40 = nhop_ipv4;
         standard_metadata.egress_spec = port;
         hdr.ipv4.ttl = hdr.ipv4.ttl + 8w255;
     }
@@ -112,7 +111,7 @@ control ingress(inout headers hdr, inout
             @defaultonly NoAction_6();
         }
         key = {
-            meta.routing_metadata.nhop_ipv4: exact @name("meta.routing_metadata.nhop_ipv4") ;
+            meta._routing_metadata_nhop_ipv40: exact @name("meta.routing_metadata.nhop_ipv4") ;
         }
         size = 512;
         default_action = NoAction_6();
