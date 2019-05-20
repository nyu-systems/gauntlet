--- dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:31:25.323861600 +0200
+++ dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:31:25.325991600 +0200
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
