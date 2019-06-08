--- dumps/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:24.221825200 +0200
+++ dumps/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:24.224282300 +0200
@@ -13,8 +13,8 @@ parser MyParser(packet_in b, out my_pack
     state start {
         bv = true;
         transition select((bit<1>)bv) {
-            (bit<1>)false: next;
-            (bit<1>)true: accept;
+            1w0: next;
+            1w1: accept;
         }
     }
     state next {
