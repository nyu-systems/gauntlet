--- dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:29:32.237839200 +0200
+++ dumps/p4_16_samples/default.p4/pruned/default-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:32.243280400 +0200
@@ -8,14 +8,14 @@ parser p0(packet_in p, out Header h) {
         b = true;
         p.extract<Header>(h);
         transition select(h.data, (bit<1>)b) {
-            (default, (bit<1>)true): next;
+            (default, 1w1): next;
             (default, default): reject;
         }
     }
     state next {
         p.extract<Header>(h);
         transition select(h.data, (bit<1>)b) {
-            (default, (bit<1>)true): accept;
+            (default, 1w1): accept;
             (default, default): reject;
             default: reject;
         }
