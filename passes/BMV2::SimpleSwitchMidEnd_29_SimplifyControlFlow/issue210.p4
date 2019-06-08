--- before_pass
+++ after_pass
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
