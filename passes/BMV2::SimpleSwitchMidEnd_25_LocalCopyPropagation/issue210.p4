--- dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:35.668130200 +0200
+++ dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:35.672926700 +0200
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
