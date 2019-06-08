--- before_pass
+++ after_pass
@@ -3,9 +3,7 @@
 control empty();
 package top(empty e);
 control Ing() {
-    bool b;
     @name("Ing.cond") action cond_0() {
-        b = true;
     }
     apply {
         cond_0();
