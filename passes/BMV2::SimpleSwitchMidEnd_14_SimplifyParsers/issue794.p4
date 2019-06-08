--- dumps/pruned/issue794-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:30:57.920008800 +0200
+++ dumps/pruned/issue794-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:30:57.923581200 +0200
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
