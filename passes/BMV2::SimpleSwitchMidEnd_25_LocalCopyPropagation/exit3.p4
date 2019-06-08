--- dumps/pruned/exit3-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:36.843662900 +0200
+++ dumps/pruned/exit3-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:36.846078500 +0200
@@ -1,5 +1,4 @@
 control ctrl(out bit<32> c) {
-    bit<32> a;
     @name("ctrl.e") action e_0() {
         exit;
     }
@@ -10,9 +9,8 @@ control ctrl(out bit<32> c) {
         default_action = e_0();
     }
     apply {
-        a = 32w0;
         c = 32w2;
-        if (a == 32w0) 
+        if (32w0 == 32w0) 
             t.apply();
         else 
             t.apply();
