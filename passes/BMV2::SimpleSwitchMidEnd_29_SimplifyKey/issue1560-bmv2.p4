--- before_pass
+++ after_pass
@@ -138,6 +138,7 @@ control cIngress(inout headers hdr, inou
         size = 8;
         default_action = NoAction_4();
     }
+    bit<16> key_0;
     @name("cIngress.t2") table t2_0 {
         actions = {
             foo1_4();
@@ -145,8 +146,8 @@ control cIngress(inout headers hdr, inou
             @defaultonly NoAction_5();
         }
         key = {
-            hdr.tcp.srcPort       : exact @name("hdr.tcp.srcPort") ;
-            hdr.ipv4.dstAddr[15:0]: selector @name("meta.hash1") ;
+            hdr.tcp.srcPort: exact @name("hdr.tcp.srcPort") ;
+            key_0          : selector @name("meta.hash1") ;
         }
         size = 16;
         default_action = NoAction_5();
@@ -155,7 +156,10 @@ control cIngress(inout headers hdr, inou
         t0_0.apply();
         t1_0.apply();
         meta._hash12 = hdr.ipv4.dstAddr[15:0];
-        t2_0.apply();
+        {
+            key_0 = hdr.ipv4.dstAddr[15:0];
+            t2_0.apply();
+        }
     }
 }
 control cEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
