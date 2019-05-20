--- dumps/p4_16_samples/issue794.p4/pruned/issue794-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:28:58.989466200 +0200
+++ dumps/p4_16_samples/issue794.p4/pruned/issue794-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:28:58.993870100 +0200
@@ -9,13 +9,7 @@ extern Random2 {
 parser caller() {
     @name("caller.rand1") Random2() rand1;
     state start {
-        transition callee_start;
-    }
-    state callee_start {
         rand1.read();
-        transition start_0;
-    }
-    state start_0 {
         transition accept;
     }
 }
