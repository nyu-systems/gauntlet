--- dumps/pruned/default-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:31:30.569278800 +0200
+++ dumps/pruned/default-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:30.572087900 +0200
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
