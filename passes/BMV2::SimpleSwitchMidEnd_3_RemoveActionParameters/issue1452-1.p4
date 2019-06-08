--- dumps/pruned/issue1452-1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:01.669280800 +0200
+++ dumps/pruned/issue1452-1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:01.647430300 +0200
@@ -1,10 +1,12 @@
 control c() {
     bit<32> x;
-    @name("c.b") action b_0(out bit<32> arg) {
+    bit<32> arg;
+    @name("c.b") action b_0() {
         arg = 32w2;
+        x = arg;
     }
     apply {
-        b_0(x);
+        b_0();
     }
 }
 control proto();
