--- before_pass
+++ after_pass
@@ -1,13 +1,7 @@
 control c() {
     bit<32> x;
-    bool hasReturned_0;
-    bit<32> arg;
     @name("c.a") action a_0() {
-        arg = x;
-        hasReturned_0 = false;
-        arg = 32w1;
-        hasReturned_0 = true;
-        x = arg;
+        x = 32w1;
     }
     apply {
         a_0();
