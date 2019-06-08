--- dumps/pruned/functors3-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:31:41.978780300 +0200
+++ dumps/pruned/functors3-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:31:41.980990500 +0200
@@ -4,13 +4,7 @@ package m(simple n);
 parser p_0(out bit<1> z) {
     bit<1> z1;
     state start {
-        transition p1_0_start;
-    }
-    state p1_0_start {
         z1 = 1w0;
-        transition start_0;
-    }
-    state start_0 {
         z = z1;
         z = 1w0;
         transition accept;
