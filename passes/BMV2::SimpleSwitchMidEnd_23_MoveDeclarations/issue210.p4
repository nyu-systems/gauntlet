--- dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:17.270589800 +0200
+++ dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:17.274312900 +0200
@@ -1,11 +1,11 @@
 #include <core.p4>
 control Ing(out bit<32> a) {
     bool b;
+    bool cond;
+    bool pred;
     @name("Ing.cond") action cond_0() {
         {
-            bool cond;
             {
-                bool pred;
                 cond = b;
                 pred = cond;
                 a = (pred ? 32w5 : a);
