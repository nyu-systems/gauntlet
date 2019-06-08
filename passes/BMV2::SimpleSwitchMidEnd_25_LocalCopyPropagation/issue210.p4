--- dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:17.278036700 +0200
+++ dumps/pruned/issue210-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:17.281655100 +0200
@@ -1,17 +1,11 @@
 #include <core.p4>
 control Ing(out bit<32> a) {
     bool b;
-    bool cond;
-    bool pred;
     @name("Ing.cond") action cond_0() {
         {
             {
-                cond = b;
-                pred = cond;
-                a = (pred ? 32w5 : a);
-                cond = !cond;
-                pred = cond;
-                a = (pred ? 32w10 : a);
+                a = (b ? 32w5 : a);
+                a = (!b ? 32w10 : a);
             }
         }
     }
