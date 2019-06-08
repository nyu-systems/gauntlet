--- dumps/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:05.578577700 +0200
+++ dumps/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:05.581767300 +0200
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
