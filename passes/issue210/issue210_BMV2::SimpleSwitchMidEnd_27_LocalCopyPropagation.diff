--- before_pass
+++ after_pass
@@ -1,17 +1,11 @@
 #include <core.p4>
 control Ing(out bit<32> a) {
     bool b_0;
-    bool cond_0;
-    bool pred;
     @name("Ing.cond") action cond() {
         {
             {
-                cond_0 = b_0;
-                pred = cond_0;
-                a = (pred ? 32w5 : a);
-                cond_0 = !cond_0;
-                pred = cond_0;
-                a = (pred ? 32w10 : a);
+                a = (b_0 ? 32w5 : a);
+                a = (!b_0 ? 32w10 : a);
             }
         }
     }
