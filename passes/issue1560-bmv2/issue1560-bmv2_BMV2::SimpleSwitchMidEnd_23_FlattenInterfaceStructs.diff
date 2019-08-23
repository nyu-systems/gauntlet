--- before_pass
+++ after_pass
@@ -53,8 +53,9 @@ struct mystruct1_t {
     bit<4> b;
 }
 struct metadata {
-    mystruct1_t mystruct1;
-    bit<16>     hash1;
+    bit<4>  _mystruct1_a0;
+    bit<4>  _mystruct1_b1;
+    bit<16> _hash12;
 }
 parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     IPv4_up_to_ihl_only_h tmp;
@@ -153,7 +154,7 @@ control cIngress(inout headers hdr, inou
         }
         key = {
             hdr.tcp.srcPort: exact @name("hdr.tcp.srcPort") ;
-            meta.hash1     : selector @name("meta.hash1") ;
+            meta._hash12   : selector @name("meta.hash1") ;
         }
         size = 16;
         default_action = NoAction_5();
@@ -161,7 +162,7 @@ control cIngress(inout headers hdr, inou
     apply {
         t0_0.apply();
         t1_0.apply();
-        meta.hash1 = hdr.ipv4.dstAddr[15:0];
+        meta._hash12 = hdr.ipv4.dstAddr[15:0];
         t2_0.apply();
     }
 }
