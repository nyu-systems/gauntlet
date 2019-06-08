--- dumps/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:59.097044200 +0200
+++ dumps/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:32:59.101896200 +0200
@@ -5,13 +5,7 @@ parser par(out bool b) {
     bit<32> x_4;
     state start {
         y = 32w0;
-        transition adder_0_start;
-    }
-    state adder_0_start {
         x_4 = y + 32w6;
-        transition start_0;
-    }
-    state start_0 {
         x = x_4;
         b = x == 32w0;
         transition accept;
