--- dumps/pruned/parser-arg-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:33:03.616403700 +0200
+++ dumps/pruned/parser-arg-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:33:03.619889000 +0200
@@ -3,23 +3,11 @@ parser Parser();
 package Package(Parser p1, Parser p2);
 parser Parser1_0() {
     state start {
-        transition Inside_start;
-    }
-    state Inside_start {
-        transition start_0;
-    }
-    state start_0 {
         transition accept;
     }
 }
 parser Parser2_0() {
     state start {
-        transition Inside_start_0;
-    }
-    state Inside_start_0 {
-        transition start_1;
-    }
-    state start_1 {
         transition accept;
     }
 }
