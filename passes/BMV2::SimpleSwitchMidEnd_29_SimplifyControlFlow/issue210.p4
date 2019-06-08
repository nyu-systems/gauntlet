--- dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:17.299798300 +0200
+++ dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:17.371790900 +0200
@@ -2,12 +2,8 @@
 control Ing(out bit<32> a) {
     bool b;
     @name("Ing.cond") action cond_0() {
-        {
-            {
-                a = (b ? 32w5 : a);
-                a = (!b ? 32w10 : a);
-            }
-        }
+        a = (b ? 32w5 : a);
+        a = (!b ? 32w10 : a);
     }
     apply {
         b = true;
