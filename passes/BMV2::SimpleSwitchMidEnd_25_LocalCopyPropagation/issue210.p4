--- before_pass
+++ after_pass
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
