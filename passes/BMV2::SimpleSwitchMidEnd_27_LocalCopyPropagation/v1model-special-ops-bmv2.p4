--- before_pass
+++ after_pass
@@ -52,11 +52,6 @@ parser ParserImpl(packet_in packet, out
 struct tuple_0 {
 }
 control ingress(inout headers_t hdr, inout meta_t meta, inout standard_metadata_t standard_metadata) {
-    bit<32> ipv4_address_0;
-    bit<8> byte0_0;
-    bit<8> byte1_0;
-    bit<8> byte2_0;
-    bit<8> byte3_0;
     standard_metadata_t smeta;
     standard_metadata_t smeta_1;
     @name(".my_drop") action my_drop() {
@@ -206,22 +201,12 @@ control ingress(inout headers_t hdr, ino
     }
     apply {
         if (standard_metadata.instance_type == 32w6) {
-            byte0_0 = 8w10;
-            byte1_0 = 8w252;
-            byte2_0 = 8w129;
-            byte3_0 = 8w2;
-            ipv4_address_0 = byte0_0 ++ byte1_0 ++ byte2_0 ++ byte3_0;
-            hdr.ipv4.srcAddr = ipv4_address_0;
+            hdr.ipv4.srcAddr = 8w10 ++ 8w252 ++ 8w129 ++ 8w2;
             meta._fwd_l2ptr0 = 32w0xe50b;
         }
         else 
             if (standard_metadata.instance_type == 32w4) {
-                byte0_0 = 8w10;
-                byte1_0 = 8w199;
-                byte2_0 = 8w86;
-                byte3_0 = 8w99;
-                ipv4_address_0 = byte0_0 ++ byte1_0 ++ byte2_0 ++ byte3_0;
-                hdr.ipv4.srcAddr = ipv4_address_0;
+                hdr.ipv4.srcAddr = 8w10 ++ 8w199 ++ 8w86 ++ 8w99;
                 meta._fwd_l2ptr0 = 32w0xec1c;
             }
             else 
