--- before_pass
+++ after_pass
@@ -3,13 +3,9 @@
 control empty();
 package top(empty e);
 control Ing() {
-    bool b;
-    bit<32> a;
     @name("Ing.cond") action cond_0() {
-        b = true;
     }
     apply {
-        a = 32w2;
         cond_0();
     }
 }
