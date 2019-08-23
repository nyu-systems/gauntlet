--- before_pass
+++ after_pass
@@ -9,9 +9,9 @@ struct Parsed_packet {
 struct meta {
     bit<32> add2;
 }
-@name("metadata") struct metadata {
-    meta    x;
-    bit<32> z;
+struct metadata {
+    bit<32> _x_add20;
+    bit<32> _z1;
 }
 control DeparserI(packet_out packet, in Parsed_packet hdr) {
     apply {
@@ -30,8 +30,8 @@ control cIngress(inout Parsed_packet hdr
     @name("cIngress.t") table t_0 {
         key = {
             hdr.x.add1: exact @name("hdr.x.add1") ;
-            m.x.add2  : exact @name("m.x.add2") ;
-            m.z       : exact @name("m.z") ;
+            m._x_add20: exact @name("m.x.add2") ;
+            m._z1     : exact @name("m.z") ;
             z_0       : exact @name("z") ;
         }
         actions = {
