--- dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:30:44.742429400 +0200
+++ dumps/p4_16_samples/issue361-bmv2.p4/pruned/issue361-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:44.745557700 +0200
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
