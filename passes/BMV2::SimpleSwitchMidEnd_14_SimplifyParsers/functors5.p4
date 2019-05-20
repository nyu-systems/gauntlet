--- dumps/p4_16_samples/functors5.p4/pruned/functors5-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:29:50.756888000 +0200
+++ dumps/p4_16_samples/functors5.p4/pruned/functors5-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:29:50.759351200 +0200
@@ -4,13 +4,7 @@ package m(simple n);
 parser p2_0(out bit<2> w) {
     bit<2> w_1;
     state start {
-        transition p1_0_start;
-    }
-    state p1_0_start {
         w_1 = 2w2;
-        transition start_0;
-    }
-    state start_0 {
         w = w_1;
         transition accept;
     }
