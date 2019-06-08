--- before_pass
+++ after_pass
@@ -152,8 +152,8 @@ control cIngress(inout headers hdr, inou
             @defaultonly NoAction_5();
         }
         key = {
-            hdr.tcp.srcPort: exact @name("hdr.tcp.srcPort") ;
-            meta.hash1     : selector @name("meta.hash1") ;
+            hdr.tcp.srcPort       : exact @name("hdr.tcp.srcPort") ;
+            hdr.ipv4.dstAddr[15:0]: selector @name("meta.hash1") ;
         }
         size = 16;
         default_action = NoAction_5();
