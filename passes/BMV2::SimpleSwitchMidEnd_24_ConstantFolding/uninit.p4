--- dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:32:33.930313600 +0200
+++ dumps/p4_16_samples/uninit.p4/pruned/uninit-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:33.933394000 +0200
@@ -26,8 +26,8 @@ parser p1(packet_in p, out Header h) {
         h.data2 = h.data3 + 32w1;
         stack[1].isValid();
         transition select((bit<1>)h.isValid()) {
-            (bit<1>)true: next1;
-            (bit<1>)false: next2;
+            1w1: next1;
+            1w0: next2;
         }
     }
     state next1 {
